module Monocle.Traversal

import Control.Applicative.Const
import Control.Monad.Identity
import Data.List1
import Data.Vect
import Monocle.Fold
import Monocle.Setter

%default total

public export
record Traversal s t a b where
  constructor T
  modifyA : {0 f : _} -> Applicative f => (a -> f b) -> s -> f t
  fold_   : Fold s t a b
  set_    : Setter s t a b

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
ToFold Traversal where toFold = fold_

public export %inline
ToSetter Traversal where
  toSetter = set_

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
(|>) : Traversal s t a b -> Traversal a b c d -> Traversal s t c d
T t1 f1 s1 |> T t2 f2 s2 = T (t1 . t2) (f1 |> f2) (s1 |> s2)

--------------------------------------------------------------------------------
--          Predefined Traversals
--------------------------------------------------------------------------------

public export %inline
traverse_ : Traversable f => Traversal (f a) (f b) a b
traverse_ = T traverse (F foldMap) (S map)

public export %inline
list_ : Traversal (List a) (List b) a b
list_ = traverse_

public export %inline
snoclist_ : Traversal (List a) (List b) a b
snoclist_ = traverse_

public export %inline
list1_ : Traversal (List1 a) (List1 b) a b
list1_ = traverse_

public export %inline
vect_ : Traversal (Vect n a) (Vect n b) a b
vect_ = traverse_
