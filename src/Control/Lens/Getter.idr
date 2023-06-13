module Control.Lens.Getter

import Control.Lens.Fold

%default total

public export
record Getter s a where
  constructor G
  get : s -> a

public export %inline
(>>>) : Getter s a -> Getter a b -> Getter s b
G f >>> G g = G $ g . f

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
find : Getter s a -> (a -> Bool) -> s -> Maybe a
find f p v = let x := f.get v in if p x then Just x else Nothing

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
F : Getter s a -> Fold s a
F f = F (. get f)
