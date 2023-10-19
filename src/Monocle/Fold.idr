module Monocle.Fold

import Data.List
import Data.SnocList

%default total

infixl 9 |>

||| A Fold is a composable data accessor, allowing us to extract
||| zero or more values of type `a` from a value of type `s`.
|||
||| Like other optics, `Folds` can be composed sequentially via operator
||| `(|>)`.
|||
||| This is a type constructor parameterized over four type parameters
||| of which two (`t` and `b`) are phantom types without any runtime
||| relevance. We need them in order to compose Folds with other
||| optics (see module `Monocle.Compose`).
|||
||| Folds are mainly useful because almost all other optics can be
||| converted to Folds (with the exception of `Setter`s).
public export
record Fold (s,t,a,b : Type) where
  constructor F
  foldMap_ : {0 m : _} -> Monoid m => (a -> m) -> s -> m

||| We can fold over every `Foldable`.
public export %inline
fold_ : Foldable t => Fold (t a) (t a) a a
fold_ = F foldMap

||| The empty Fold, which always yields zero values.
public export %inline
empty : Fold s t a b
empty = F $ \_,_ => neutral

||| Sequential composition of Folds.
public export %inline
(|>) : Fold s t a b -> Fold a b c d -> Fold s t c d
F f |> F g = F $ f . g

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting other optics to Folds.
public export
interface ToFold (0 o : Type -> Type -> Type -> Type -> Type) where
  toFold : o s t a b -> Fold s t a b

public export %inline
ToFold Fold where toFold = id

--------------------------------------------------------------------------------
--          Monoids
--------------------------------------------------------------------------------

public export
[SFirst] Semigroup (Maybe a) where
  Nothing <+> y = y
  x       <+> _ = x

public export
[First] Monoid (Maybe a) using SFirst where neutral = Nothing

public export
[SLast] Semigroup (Maybe a) where
  x <+> Nothing = x
  _ <+> y       = y

public export
[Last] Monoid (Maybe a) using SLast where neutral = Nothing

--------------------------------------------------------------------------------
--          Utility Functions
--------------------------------------------------------------------------------

||| Use a Fold to extract data from a source value and accumulate it
||| via a `Monoid`.
public export %inline
foldMap : Monoid m => ToFold o => o s t a b -> (a -> m) -> s -> m
foldMap f = foldMap_ (toFold f)

||| Use a Fold to extract and accumulate data with a `Monoid` implementation
||| from a source value.
public export %inline
fold : ToFold o => Monoid a => o s t a b -> s -> a
fold f = foldMap f id

||| Use a Fold to extract data from a source value and store it in a `List`.
public export %inline
asList : ToFold o => o s t a b -> s -> List a
asList f = foldMap f pure

||| Use a Fold to extract data from a source value and
||| store it in a `SnocList`.
public export %inline
asSnocList : ToFold o => o s t a b -> s -> SnocList a
asSnocList f = foldMap f pure

||| Use a Fold to try and extract the first piece of data from a source value.
public export %inline
first : ToFold o => o s t a b -> s -> Maybe a
first f = foldMap @{First} f Just

||| Use a Fold to try and extract the last piece of data from a source value.
public export
last : ToFold o => o s t a b -> s -> Maybe a
last f = foldMap @{Last} f Just

||| Use a Fold to try and extract the first piece of data
||| fulfilling a predicate from a source value.
public export
find : ToFold o => o s t a b -> (a -> Bool) -> s -> Maybe a
find f g = foldMap @{First} f (\x => if g x then Just x else Nothing)
