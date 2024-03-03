module Monocle.Prism

import Monocle.Fold
import Monocle.Optional
import Monocle.Setter
import Monocle.Traversal
import Data.List.Quantifiers.Extra
import Data.List1
import Data.Maybe

%default total

||| A Prism is the categorical dual of a Lens: While a Lens allows
||| us to extract values from a larger type, a Prism allows us to inject
||| values into a larger type, while extracting such a value might not
||| be possible.
|||
||| Prisms are therefore a natural fit for inspecting sum types,
||| (as opposed to lenses, which are preferrably used for product types),
||| where we typically have one Prism per data constructor.
|||
||| An other use case where Prisms shine are refinement type, where
||| "injecting" a value means extracting a value of the parent type from
||| refinement type. An example for this is the `nat` Prism, which allows
||| us to convert ("inject") a `Nat` into an `Integer`, while extracting a
||| `Nat` from an `Integer` might fail.
|||
||| A Prism is parameterized over four parameters, because in general
||| we can not only try and extract a value from some object
||| but also refine the object in case extraction fails.
||| Consider lens `fst`, where `s` corresponds to `(a,c)` and
||| `t` corresponds to `(b,c)`. Accordingly, if we have a function from
||| `a` to `b`, we can convert a pair of type `(a,c)` to one of type `(b,c)`.
public export
record Prism s t a b where
  constructor P
  getOrModify : s -> Either t a
  reverseGet  : b -> t

||| Convenience alias for monomorphic Prisms, which do not allow
||| us to change the value and source types.
public export
0 Prism' : (s,a : Type) -> Type
Prism' s a = Prism s s a a

||| Convenience constructor for monomorphic Prisms.
public export
prism : (a -> Maybe b) -> (b -> a) -> Prism' a b
prism f = P (\v => maybe (Left v) Right (f v))

||| Adjust the focus of a Prism with an effectful computation.
public export
mapA : Applicative f => Prism s t a b -> (a -> f b) -> s -> f t
mapA (P g r) f v = either pure (map r . f) (g v)

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting other optics to Prisms.
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
  toOptional (P g r) = O g (\f => either id (r . f) . g)

public export
ToSetter Prism where
  toSetter (P g r) = S $ \f,vs => either id (r . f) (g vs)

public export
ToFold Prism where
  toFold (P g r) = F $ \f => either (const neutral) f . g

public export
ToTraversal Prism where
  toTraversal o = T (mapA o) (toFold o) (toSetter o)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Sequential composition of Prisms.
public export
(|>) : Prism s t a b -> Prism a b c d -> Prism s t c d
P g1 r1 |> P g2 r2 =
  P (\v => g1 v >>= mapFst r1 . g2)
    (r1 . r2)

--------------------------------------------------------------------------------
--          Predefined Prisms
--------------------------------------------------------------------------------

||| A Prism focussing on the `Left` data constructor of `Either a b`.
public export
left' : Prism (Either a b) (Either c b) a c
left' = P (either Right (Left . Right)) Left

||| Monomorphic version of `left'`.
|||
||| This can improve type inference for those cases where the versatility
||| of `left'` is not needed.
public export %inline
left : Prism' (Either a b) a
left = left'

||| A Prism focussing on the `Right` data constructor of `Either a b`.
public export
right' : Prism (Either a b) (Either a c) b c
right' = P (either (Left . Left) Right) Right

||| Monomorphic version of `right'`.
|||
||| This can improve type inference for those cases where the versatility
||| of `right'` is not needed.
public export %inline
right : Prism' (Either a b) b
right = right'

||| A Prism focussing on the `Just` data constructor of a `Maybe`.
public export
just' : Prism (Maybe a) (Maybe b) a b
just' = P (maybe (Left Nothing) Right) Just

||| Monomorphic version of `just'`.
|||
||| This can improve type inference for those cases where the versatility
||| of `just'` is not needed.
public export %inline
just : Prism' (Maybe a) a
just = just'

||| A Prism focussing on the `Nothing` data constructor of a `Maybe`.
public export
nothing : Prism' (Maybe a) ()
nothing = P (maybe (Right ()) (Left . Just)) (const Nothing)

||| A Prism focussing on the `(::)` ("cons") data constructor of a
||| `List`.
public export
cons' : Prism (List a) (List b) (a,List a) (b,List b)
cons' = P (\case Nil => Left Nil; h::t => Right (h,t)) (uncurry (::))

||| A Prism focussing on the `Nil` data constructor of a
||| `List`.
public export
nil : Prism' (List a) ()
nil = prism (\case Nil => Just (); _ => Nothing) (const Nil)

||| Monomorphic version of `cons'`.
|||
||| This can improve type inference for those cases where the versatility
||| of `cons'` is not needed.
public export %inline
cons : Prism' (List a) (a,List a)
cons = cons'

||| A Prism focussing on the `(:<)` ("snoc") data constructor of a
||| `SnocList`.
public export
snoc' : Prism (SnocList a) (SnocList b) (SnocList a,a) (SnocList b,b)
snoc' = P (\case Lin => Left Lin; i :< l => Right (i,l)) (uncurry (:<))

||| A Prism focussing on the `Lin` data constructor of a
||| `SnocList`.
public export
lin : Prism' (SnocList a) ()
lin = prism (\case Lin => Just (); _ => Nothing) (const Lin)

||| Monomorphic version of `snoc'`.
|||
||| This can improve type inference for those cases where the versatility
||| of `snoc'` is not needed.
public export %inline
snoc : Prism' (SnocList a) (SnocList a,a)
snoc = snoc'

||| A Prism for converting between non-empty lists and regular lists.
public export
list1' : Prism (List a) (List b) (List1 a) (List1 b)
list1' = P (\case Nil => Left Nil; h::t => Right (h ::: t)) forget

public export %inline
list1 : Prism' (List a) (List1 a)
list1 = list1'

||| A Prism focussing on a single option in a heterogeneous sum.
public export
sum :
     {0 ks : List k}
  -> {0 f  : k -> Type}
  -> (0 t : k)
  -> {auto e : Elem t ks}
  -> Prism' (Any f ks) (f t)
sum t = prism project' inject

public export
anyHead : Prism' (Any f (k::ks)) (f k)
anyHead = prism (\case Here v => Just v; _ => Nothing) Here

public export
anyTail : Prism' (Any f (k::ks)) (Any f ks)
anyTail = prism (\case There v => Just v; _ => Nothing) There

||| A Prism focussing on non-negative integers.
public export
nat : Prism' Integer Nat
nat = prism (\x => toMaybe (x >= 0) (cast x)) cast
