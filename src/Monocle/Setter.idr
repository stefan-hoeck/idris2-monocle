module Monocle.Setter

import Control.Monad.State
import Data.Contravariant
import Data.SnocList
import Monocle.Fold

%default total

||| A Setter allows us to update zero or more values in a
||| larger data type.
|||
||| Possible examples include updating single record fields, mapping
||| a function over the values in a `List` (or any other `Functor`),
||| or converting the characters in a string.
|||
||| A Setter is parameterized over four parameters, because in general
||| we could not only update a value but also its type with an updating
||| function. Consider Setter `io`, where `s` corresponds to `IO a` and
||| `t` corresponds to `IO b`. Accordingly, if we have a function from
||| `a` to `b`, we can convert an `IO a` to an `IO b`.
public export
record Setter s t a b where
  constructor S
  over_ : (a -> b) -> s -> t

||| Convenience alias for monomorphic setters, which do not allow
||| us to change the value and source types.
public export
0 Setter' : (s,a : Type) -> Type
Setter' s a = Setter s s a a

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting other optics to setters. With the exception
||| of Fold and Getter, all optics in this library have an implementation
||| of `ToSetter`.
public export
interface ToSetter (0 o : Type -> Type -> Type -> Type -> Type) where
  toSetter : o s t a b -> Setter s t a b

public export %inline
ToSetter Setter where toSetter = id

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Use a Setter to update the data stored in a source value.
public export %inline
over : ToSetter o => o s t a b -> (a -> b) -> s -> t
over f = over_ (toSetter f)

||| Use a Setter to set the data stored in a source value.
public export %inline
set : ToSetter o => o s t a b -> b -> s -> t
set f = over (toSetter f) . const

||| Sequential composition of setters.
public export %inline
(|>) : Setter s t a b -> Setter a b c d -> Setter s t c d
S f |> S g = S $ f . g

--------------------------------------------------------------------------------
--          Predefined Setters
--------------------------------------------------------------------------------

||| Every `Functor` gives rise to a polymorphic Setter via `map`.
public export %inline
map_ : Functor f => Setter (f a) (f b) a b
map_ = S map

||| Every contravariant functor gives rise to a polymorphic Setter via
||| `contramap`.
public export %inline
contramap_ : Contravariant f => Setter (f a) (f b) b a
contramap_ = S contramap

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

||| Modify the current state with a setter
export %inline
overST : Monad m => Setter' s a -> (a -> a) -> StateT s m ()
overST s f = modify (s.over_ f)

||| Modify the current state with a setter
export %inline
setST : Monad m => Setter' s a -> a -> StateT s m ()
setST s = overST s . const
