module Control.Lens.Prism

import Control.Lens.Fold
import Control.Lens.Optional
import Control.Lens.Setter
import Control.Lens.Traversal
import Data.List.Quantifiers.Extra

%default total

public export
record Prism s t a b where
  constructor P
  getOrModify : s -> Either t a
  reverseGet  : b -> t

public export
0 Prism' : (s,a : Type) -> Type
Prism' s a = Prism s s a a

public export
prism : (a -> Maybe b) -> (b -> a) -> Prism' a b
prism f = P (\v => maybe (Left v) Right (f v))

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface ToPrism (0 o : Type -> Type -> Type -> Type -> Type) where
  toPrism : o s t a b -> Prism s t a b

public export %inline
ToPrism Prism where toPrism = id

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export
ToOptional Prism where
  toOptional (P g r) = O g (const . r)

public export
ToSetter Prism where
  toSetter (P g r) = S $ \f,vs => either id (r . f) (g vs)

public export
ToFold Prism where
  toFold (P g r) = F $ \f => either (const neutral) f . g

public export
ToTraversal Prism where
  toTraversal (P g r) = T $ \f,v => case g v of
    Left x  => pure x
    Right x => r <$> f x

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
(|>) : Prism s t a b -> Prism a b c d -> Prism s t c d
P g1 r1 |> P g2 r2 =
  P (\v => g1 v >>= mapFst r1 . g2)
    (r1 . r2)

--------------------------------------------------------------------------------
--          Predefined Prisms
--------------------------------------------------------------------------------

public export
left' : Prism (Either a b) (Either c b) a c
left' = P (either Right (Left . Right)) Left

public export %inline
left : Prism' (Either a b) a
left = left'

public export
right' : Prism (Either a b) (Either a c) b c
right' = P (either (Left . Left) Right) Right

public export %inline
right : Prism' (Either a b) b
right = right'

public export
just' : Prism (Maybe a) (Maybe b) a b
just' = P (maybe (Left Nothing) Right) Just

public export %inline
just : Prism' (Maybe a) a
just = just'

public export
nothing : Prism' (Maybe a) ()
nothing = P (maybe (Right ()) (Left . Just)) (const Nothing)

public export
cons' : Prism (List a) (List b) (a,List a) (b,List b)
cons' = P (\case Nil => Left Nil; h::t => Right (h,t)) (uncurry (::))

public export %inline
cons : Prism' (List a) (a,List a)
cons = cons'

public export
snoc' : Prism (SnocList a) (SnocList b) (SnocList a,a) (SnocList b,b)
snoc' = P (\case Lin => Left Lin; i :< l => Right (i,l)) (uncurry (:<))

public export %inline
snoc : Prism' (SnocList a) (SnocList a,a)
snoc = snoc'

public export
sum :
     {0 ks : List k}
  -> {0 f  : k -> Type}
  -> (0 t : k)
  -> {auto e : Elem t ks}
  -> Prism' (Any f ks) (f t)
sum t = prism project' inject
