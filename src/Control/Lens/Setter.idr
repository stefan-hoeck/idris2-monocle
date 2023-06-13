module Control.Lens.Setter

import Control.Lens.Fold
import Data.Contravariant
import Data.SnocList

%default total

public export
record Setter s t a b where
  constructor S
  over_ : (a -> b) -> s -> t

public export
0 Setter' : (s,a : Type) -> Type
Setter' s a = Setter s s a a

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface ToSetter (0 o : Type -> Type -> Type -> Type -> Type) where
  toSetter : o s t a b -> Setter s t a b

public export %inline
ToSetter Setter where toSetter = id

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
over : ToSetter o => o s t a b -> (a -> b) -> s -> t
over f = over_ (toSetter f)

public export %inline
set : ToSetter o => o s t a b -> b -> s -> t
set f = over (toSetter f) . const

public export %inline
(|>) : Setter s t a b -> Setter a b c d -> Setter s t c d
S f |> S g = S $ f . g

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
