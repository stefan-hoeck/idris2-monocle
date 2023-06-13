module Monocle.Traversal

import Control.Applicative.Const
import Control.Monad.Identity
import Monocle.Fold
import Monocle.Setter

%default total

public export
record Traversal s t a b where
  constructor T
  modifyA : {0 f : _} -> Applicative f => (a -> f b) -> s -> f t

public export
0 Traversal' : (s,a : Type) -> Type
Traversal' s a = Traversal s s a a

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface ToTraversal (0 o : Type -> Type -> Type -> Type -> Type) where
  toTraversal : o s t a b -> Traversal s t a b

public export %inline
ToTraversal Traversal where toTraversal = id

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
ToFold Traversal where
  toFold t = F $ \f => runConst . t.modifyA (MkConst . f)

public export %inline
ToSetter Traversal where
  toSetter t = S $ \f => runIdentity . t.modifyA (Id . f)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
(|>) : Traversal s t a b -> Traversal a b c d -> Traversal s t c d
T f |> T g = T $ f . g

--------------------------------------------------------------------------------
--          Predefined Traversals
--------------------------------------------------------------------------------

public export %inline
traverse_ : Traversable f => Traversal (f a) (f b) a b
traverse_ = T traverse

public export %inline
chars : Traversal' String Char
chars = T $ \f => map pack . traverse f . unpack
