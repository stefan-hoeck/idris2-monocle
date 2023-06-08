module Control.Lens.Fold

import Data.SnocList

%default total

infixr 1 >>>

public export
record Fold s a where
  constructor F
  foldMap : {0 m : _} -> Monoid m => (a -> m) -> s -> m

public export %inline
fold_ : Foldable t => Fold (t a) a
fold_ = F foldMap

public export %inline
(>>>) : Fold s a -> Fold a b -> Fold s b
F f >>> F g = F $ f . g

--------------------------------------------------------------------------------
--          Utility Functions
--------------------------------------------------------------------------------

public export %inline
fold : Monoid a => Fold s a -> s -> a
fold f = foldMap f id

public export %inline
list : Fold s a -> s -> List a
list f = foldMap f pure

public export %inline
snocList : Fold s a -> s -> SnocList a
snocList f = foldMap f pure

public export
first : Fold s a -> s -> Maybe a
first f v = case list f v of (h::_) => Just h; Nil => Nothing

public export
last : Fold s a -> s -> Maybe a
last f v = case snocList f v of (_ :< l) => Just l; Lin => Nothing

public export
select : (a -> Bool) -> Fold a a
select f = F $ \g,x => if f x then g x else neutral

public export
empty : Fold s a
empty = F $ \_,_ => neutral
