module Control.Lens.Optional

import Control.Lens.Fold
import Control.Lens.Setter
import Control.Lens.Traversal

%default total

public export
record Optional s t a b where
  constructor O
  getOrModify : s -> Either t a
  replace     : b -> s -> t

public export
0 Optional' : (s,a : Type) -> Type
Optional' s a = Optional s s a a

public export
optional : (s -> Maybe a) -> (a -> s -> s) -> Optional' s a
optional f g = O (\v => maybe (Left v) Right (f v)) g

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

public export
ToSetter Optional where
  toSetter (O g r) = S $ \f,vs => either id (\va => r (f va) vs) (g vs)

public export
ToFold Optional where
  toFold (O g r) = F $ \f => either (const neutral) f . g

public export
ToTraversal Optional where
  toTraversal (O g r) = T $ \f,v => case g v of
    Left x  => pure x
    Right x => map (`r` v) (f x)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
(|>) : Optional s t a b -> Optional a b c d -> Optional s t c d
O g1 r1 |> O g2 r2 =
  O (\v => g1 v >>= mapFst (`r1` v) . g2)
    (\vd,vs => either id (\va => r1 (r2 vd va) vs) (g1 vs))

--------------------------------------------------------------------------------
--          Predefined Optionals
--------------------------------------------------------------------------------

public export
getIx : Nat -> List a -> Maybe a
getIx 0     (h::_) = Just h
getIx (S k) (_::t) = getIx k t
getIx _     Nil    = Nothing

public export
setIx : Nat -> a -> List a -> List a
setIx 0     x (h::xs) = x :: xs
setIx (S k) x (h::xs) = h :: setIx k x xs
setIx _     _ []      = []

public export
ix : Nat -> Optional' (List a) a
ix n = optional (getIx n) (setIx n)

public export
select : (a -> Bool) -> Optional' a a
select p =
  optional
    (\v => if p v then Just v else Nothing)
    (\n,o => if p o then n else o)

public export
eqBy : Eq b => b -> (a -> b) -> Optional' a a
eqBy v f = select ((v ==) . f)
