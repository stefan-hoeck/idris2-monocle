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
--          Conversions
--------------------------------------------------------------------------------

public export
S : Optional s t a b -> Setter s t a b
S (O g r) = S $ \f,vs => either id (\va => r (f va) vs) (g vs)

public export
F : Optional s t a b -> Fold s a
F (O g r) = F $ \f => either (const neutral) f . g

public export
T : Optional s t a b -> Traversal s t a b
T (O g r) = T $ \f,v => case g v of
  Left x  => pure x
  Right x => map (`r` v) (f x)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
(>>>) : Optional s t a b -> Optional a b c d -> Optional s t c d
O g1 r1 >>> O g2 r2 =
  O (\v => g1 v >>= mapFst (`r1` v) . g2)
    (\vd,vs => either id (\va => r1 (r2 vd va) vs) (g1 vs))

--------------------------------------------------------------------------------
--          Predefined Optionals
--------------------------------------------------------------------------------

public export
ix : Nat -> List a -> Maybe a
ix 0     (h::_) = Just h
ix (S k) (_::t) = ix k t
ix _     Nil    = Nothing

public export
setIx : Nat -> a -> List a -> List a
setIx 0     x (h::xs) = x :: xs
setIx (S k) x (h::xs) = h :: setIx k x xs
setIx _     _ []      = []

public export
index : Nat -> Optional' (List a) a
index n = optional (ix n) (setIx n)

public export
filter : (a -> Bool) -> Optional' a a
filter p =
  optional
    (\v => if p v then Just v else Nothing)
    (\n,o => if p o then n else o)
