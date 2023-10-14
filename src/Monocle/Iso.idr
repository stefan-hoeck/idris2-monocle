module Monocle.Iso

import Monocle.Fold
import Monocle.Getter
import Monocle.Lens
import Monocle.Optional
import Monocle.Prism
import Monocle.Setter
import Monocle.Traversal
import Data.List.Quantifiers
import Data.Maybe

%default total

||| An `Iso` describes an isomorphism between two types.
|||
||| Two types are isomorphic, if there is a lossless conversion
||| from one to the other and vice versa. Examples include the
||| (monomorphic) isomorphism from `String` to `List Char` and the
||| (polymorphic) isomorphism from `Either a b` to `Either b a`.
|||
||| Isomorphisms must obey two identity laws:
|||
||| `get_ . reverseGet` must be the identity function. The same holds
||| for `reverseGet . get_`.
public export
record Iso s t a b where
  constructor I
  get_       : s -> a
  reverseGet : b -> t

||| Convenience alias for monomorphic `Iso`s, which do not allow
||| us to change the value and source types.
public export
0 Iso' : (s,a : Type) -> Type
Iso' s a = Iso s s a a

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting other optics to `Iso`s.
public export
interface ToIso (0 o : Type -> Type -> Type -> Type -> Type) where
  toIso : o s t a b -> Iso s t a b

public export %inline
ToIso Iso where toIso = id

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export
ToPrism Iso where
  toPrism (I g r) = P (Right . g) r

public export
ToOptional Iso where
  toOptional (I g r) = O (Right . g) (\f => r . f . g)

public export
ToSetter Iso where
  toSetter (I g r) = S $ \f => r . f . g

public export %inline
ToFold Iso where
  toFold (I g r) = F (. g)

public export
ToGetter Iso where
  toGetter (I g r) = G g

public export
ToTraversal Iso where
  toTraversal i =
    T (\f,v => i.reverseGet <$> f (i.get_ v))
      (toFold i)
      (toSetter i)

public export %inline
ToLens Iso where
  toLens (I g r) = L g $ \f => r . f . g

--------------------------------------------------------------------------------
--          Utilitis
--------------------------------------------------------------------------------

||| Isomorphisms are symmetric: If `x` is isomorphic to `y` then `y` is
||| isomorphic to `x`. This function describes this symmetry.
public export %inline
rev : Iso s t a b -> Iso b a t s
rev (I f g) = I g f

||| Sequential composition of `Iso`s.
|||
||| This describes the transitivity of isomorphisms: If `x` is isomorphic to
||| `y` and `y` is isomorhic to `z`, then `x` is isomorphic to `z`.
public export
(|>) : Iso s t a b -> Iso a b c d -> Iso s t c d
I f1 g1 |> I f2 g2 = I (f2 . f1) (g1 . g2)

--------------------------------------------------------------------------------
--          Isomorphisms
--------------------------------------------------------------------------------

||| Isomorphisms are reflexive: Every type is trivially isomorphic to itself.
export %inline
identity : Iso' a a
identity = I id id

||| The identity lens, derived from the corresponding isomorphism.
export %inline
idL : Lens' a a
idL = toLens identity

||| Isomorphism between `List Char` and `String`.
export
pack : Iso' (List Char) String
pack = I pack unpack

||| Isomorphism between `String` and `List Char`.
export
unpack : Iso' String (List Char)
unpack = I unpack pack

||| Isomorphism between `SnocList` and `List`.
export
chips : Iso (SnocList a) (SnocList b) (List a) (List b)
chips = I (<>> []) ([<] <><)

||| Isomorphism between `List` and `SnocList`.
export
fish : Iso (List a) (List b) (SnocList a) (SnocList b)
fish = I ([<] <><) (<>> [])

||| Isomorphism between pairs with their values swapped.
export
swap : Iso (a,b) (c,d) (b,a) (d,c)
swap = I swap swap

||| Isomorphism between binary functions with their arguments
||| swapped.
export
flip : Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flip = I flip flip

||| Isomorphism between binary functions and functions taking
||| a pair of values as their argument.
export
uncurry : Iso (a -> b -> c) (d -> e -> f) ((a,b) -> c) ((d,e) -> f)
uncurry = I uncurry curry

||| Isomorphism between functions taking a pair as their argument
||| and binary functions.
export
curry : Iso ((a,b) -> c) ((d,e) -> f) (a -> b -> c) (d -> e -> f)
curry = I curry uncurry

||| Isomorphism between `Either a b` and `Either b a`.
export
swapE : Iso (Either a b) (Either c d) (Either b a) (Either d c)
swapE = I (either Right Left) (either Right Left)

||| Given a default value of type `a`, we can create an isomorphism between
||| `Maybe a` and values of type `a`.
|||
||| This wraps every value of type `a` in a `Just`. In the other direction,
||| we use `fromMaybe` with the provided default value to extract a value
||| from a `Nothing`.
export
withDefault : a -> Iso' (Maybe a) a
withDefault v = I (fromMaybe v) Just

||| Isomorphism between `Either Void a` and `a`: The `Left` case
||| is impossible because `Void` is uninhabited.
export
leftVoid : Iso (Either Void a) (Either Void b) a b
leftVoid = I (either absurd id) Right

||| Isomorphism between `Either a Void` and `a`: The `Right` case
||| is impossible because `Void` is uninhabited.
export
rightVoid : Iso (Either a Void) (Either b Void) a b
rightVoid = I (either id absurd) Left

||| Isomorphism between a unary sum type and the wrapped value.
export
any1 : Iso (Any f [a]) (Any g [b]) (f a) (g b)
any1 = I (\case Here v => v) Here
