module Control.Lens.Setter

import Control.Lens.Fold
import Data.Contravariant
import Data.SnocList

%default total

public export
record Setter s t a b where
  constructor S
  mod : (a -> b) -> s -> t

public export
0 Setter' : (s,a : Type) -> Type
Setter' s a = Setter s s a a

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
set : Setter s t a b -> b -> s -> t
set f = f.mod . const

public export %inline
(>>>) : Setter s t a b -> Setter a b c d -> Setter s t c d
S f >>> S g = S $ f . g

--------------------------------------------------------------------------------
--          Predefined Setters
--------------------------------------------------------------------------------

public export %inline
map_ : Functor f => Setter (f a) (f b) a b
map_ = S map

public export %inline
contramap_ : Contravariant f => Setter (f a) (f b) b a
contramap_ = S contramap

public export %inline
chars : Setter' String Char
chars = S $ \f => pack . map f . unpack
