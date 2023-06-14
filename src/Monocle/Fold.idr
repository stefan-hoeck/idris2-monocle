module Monocle.Fold

import Data.List
import Data.SnocList

%default total

infixl 9 |>

public export
record Fold (s,t,a,b : Type) where
  constructor F
  foldMap_ : {0 m : _} -> Monoid m => (a -> m) -> s -> m

public export %inline
fold_ : Foldable t => Fold (t a) (t a) a a
fold_ = F foldMap

public export %inline
empty : Fold s t a b
empty = F $ \_,_ => neutral

public export %inline
(|>) : Fold s t a b -> Fold a b c d -> Fold s t c d
F f |> F g = F $ f . g

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

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

public export %inline
foldMap : Monoid m => ToFold o => o s t a b -> (a -> m) -> s -> m
foldMap f = foldMap_ (toFold f)

public export %inline
fold : ToFold o => Monoid a => o s t a b -> s -> a
fold f = foldMap f id

public export %inline
asList : ToFold o => o s t a b -> s -> List a
asList f = foldMap f pure

public export %inline
asSnocList : ToFold o => o s t a b -> s -> SnocList a
asSnocList f = foldMap f pure

public export %inline
first : ToFold o => o s t a b -> s -> Maybe a
first f = foldMap @{First} f Just

public export
last : ToFold o => o s t a b -> s -> Maybe a
last f = foldMap @{Last} f Just

public export
find : ToFold o => o s t a b -> (a -> Bool) -> s -> Maybe a
find f g = foldMap @{First} f (\x => if g x then Just x else Nothing)
