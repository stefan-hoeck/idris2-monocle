module Control.Lens.Traversal

import Control.Applicative.Const
import Control.Lens.Fold
import Control.Lens.Setter
import Control.Monad.Identity

%default total

public export
record Traversal s t a b where
  constructor T
  modifyA : {0 f : _} -> Applicative f => (a -> f b) -> s -> f t

public export
0 Traversal' : (s,a : Type) -> Type
Traversal' s a = Traversal s s a a

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
F : Traversal s t a b -> Fold s a
F t = F $ \f => runConst . t.modifyA (MkConst . f)

public export %inline
S : Traversal s t a b -> Setter s t a b
S t = S $ \f => runIdentity . t.modifyA (Id . f)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
(>>>) : Traversal s t a b -> Traversal a b c d -> Traversal s t c d
T f >>> T g = T $ f . g

--------------------------------------------------------------------------------
--          Predefined Traversals
--------------------------------------------------------------------------------

public export %inline
traverse_ : Traversable f => Traversal (f a) (f b) a b
traverse_ = T traverse

public export %inline
chars : Traversal' String Char
chars = T $ \f => map pack . traverse f . unpack
