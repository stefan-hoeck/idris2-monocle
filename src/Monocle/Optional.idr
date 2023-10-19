module Monocle.Optional

import Data.List
import Monocle.Fold
import Monocle.Setter
import Monocle.Traversal

%default total

||| An Optional allows us to focus on a single piece of
||| information in a larger data object that might or might not
||| be there.
|||
||| An Optional is related to but less powerful than a Prism, because
||| it does not allow us to directly inject a value into a larger data
||| object, but only supports updating such a value if it exists.
|||
||| Optionals play an important role when we sequentially combine different
||| types of optics: The sequential composition of a Lens with a Prism or
||| vice verca results in an optional: We can no longer be certain that
||| the value we focus on is still there (the Prism prevents that), nor can
||| we directly inject the value into the larger data object
||| (the Lens prevents that).
public export
record Optional s t a b where
  constructor O
  getOrModify : s -> Either t a
  replace     : (a -> b) -> s -> t

||| Convenience alias for monomorphic Optionals, which do not allow
||| us to change the value and source types.
public export
0 Optional' : (s,a : Type) -> Type
Optional' s a = Optional s s a a

||| Utility constructor for monomorphic optionals.
public export
optional : (s -> Maybe a) -> ((a -> a) -> s -> s) -> Optional' s a
optional f g = O (\v => maybe (Left v) Right (f v)) g

||| Adjust the focus sof an Optional with an effectful computation.
public export
mapA : Applicative f => Optional s t a b -> (a -> f b) -> s -> f t
mapA (O g r) f v =
  case g v of
    Left x  => pure x
    Right x => map (\vb => r (const vb) v) (f x)

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting other optics to Optionals.
public export
interface ToOptional (0 o : Type -> Type -> Type -> Type -> Type) where
  toOptional : o s t a b -> Optional s t a b

public export %inline
ToOptional Optional where toOptional = id

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
ToSetter Optional where
  toSetter (O g r) = S r

public export
ToFold Optional where
  toFold (O g r) = F $ \f => either (const neutral) f . g

public export
ToTraversal Optional where
  toTraversal o = T (mapA o) (toFold o) (toSetter o)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Sequential composition of Optionals.
public export
(|>) : Optional s t a b -> Optional a b c d -> Optional s t c d
O g1 r1 |> O g2 r2 =
  O (\v => g1 v >>= mapFst (\vb => r1 (const vb) v) . g2)
    (r1 . r2)

--------------------------------------------------------------------------------
--          Predefined Optionals
--------------------------------------------------------------------------------

||| The empty Optional, which does not focus on anything at all.
public export
emptyO : Optional' s a
emptyO = O Left (const id)

||| Tries to extract a value at the given index from a List.
public export
getIx : Nat -> List a -> Maybe a
getIx 0     (h::_) = Just h
getIx (S k) (_::t) = getIx k t
getIx _     Nil    = Nothing

||| Modifies the value at the given index in a List.
|||
||| Returns the unchanged List if the index is out of bounds.
public export
modIx : Nat -> (a -> a) -> List a -> List a
modIx 0     f (h::xs) = f h :: xs
modIx (S k) f (h::xs) = h :: modIx k f xs
modIx _     _ []      = []

||| An Optional focussing on the n-th element in a List.
public export
ix : Nat -> Optional' (List a) a
ix n = optional (getIx n) (modIx n)

||| An Optional for focussing on those values that fulfill a given
||| predicate.
public export
select : (a -> Bool) -> Optional' a a
select p =
  optional
    (\v => if p v then Just v else Nothing)
    (\f,o => if p o then f o else o)

||| An Optional for focussing on those values that are equivalent to `v`
||| according to the given comparison function.
public export %inline
eqBy : Eq b => (v : b) -> (a -> b) -> Optional' a a
eqBy v f = select ((v ==) . f)

public export
modWhere : SnocList a -> (a -> Bool) -> (a -> a) -> List a -> List a
modWhere sa f g []        = sa <>> []
modWhere sa f g (x :: xs) =
  if f x then sa <>> (g x :: xs) else modWhere (sa :< x) f g xs

||| An Optional for focussing on the first value in a list
||| that fulfills the given predicate.
public export %inline
first : (a -> Bool) -> Optional' (List a) a
first f = optional (find f) (modWhere [<] f)

||| An Optional for focussing on the first value in a List
||| that is equivalent to `v` according to the given comparison function.
public export %inline
eqFirst : Eq b => b -> (a -> b) -> Optional' (List a) a
eqFirst v f = first ((v ==) . f)
