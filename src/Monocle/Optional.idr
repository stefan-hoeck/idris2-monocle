module Monocle.Optional

import Data.List
import Monocle.Fold
import Monocle.Setter
import Monocle.Traversal

%default total

public export
record Optional s t a b where
  constructor O
  getOrModify : s -> Either t a
  replace     : (a -> b) -> s -> t

public export
0 Optional' : (s,a : Type) -> Type
Optional' s a = Optional s s a a

public export
optional : (s -> Maybe a) -> ((a -> a) -> s -> s) -> Optional' s a
optional f g = O (\v => maybe (Left v) Right (f v)) g

public export
mapA : Applicative f => Optional s t a b -> (a -> f b) -> s -> f t
mapA (O g r) f v = case g v of
  Left x  => pure x
  Right x => map (\vb => r (const vb) v) (f x)

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

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

public export
(|>) : Optional s t a b -> Optional a b c d -> Optional s t c d
O g1 r1 |> O g2 r2 =
  O (\v => g1 v >>= mapFst (\vb => r1 (const vb) v) . g2)
    (r1 . r2)

--------------------------------------------------------------------------------
--          Predefined Optionals
--------------------------------------------------------------------------------

public export
getIx : Nat -> List a -> Maybe a
getIx 0     (h::_) = Just h
getIx (S k) (_::t) = getIx k t
getIx _     Nil    = Nothing

public export
modIx : Nat -> (a -> a) -> List a -> List a
modIx 0     f (h::xs) = f h :: xs
modIx (S k) f (h::xs) = h :: modIx k f xs
modIx _     _ []      = []

public export
ix : Nat -> Optional' (List a) a
ix n = optional (getIx n) (modIx n)

public export
select : (a -> Bool) -> Optional' a a
select p =
  optional
    (\v => if p v then Just v else Nothing)
    (\f,o => if p o then f o else o)

public export %inline
eqBy : Eq b => b -> (a -> b) -> Optional' a a
eqBy v f = select ((v ==) . f)

public export
modWhere : SnocList a -> (a -> Bool) -> (a -> a) -> List a -> List a
modWhere sa f g []        = sa <>> []
modWhere sa f g (x :: xs) =
  if f x then sa <>> (g x :: xs) else modWhere (sa :< x) f g xs

public export %inline
first : (a -> Bool) -> Optional' (List a) a
first f = optional (find f) (modWhere [<] f)

public export %inline
eqFirst : Eq b => b -> (a -> b) -> Optional' (List a) a
eqFirst v f = first ((v ==) . f)
