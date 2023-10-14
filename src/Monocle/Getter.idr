module Monocle.Getter

import Monocle.Fold

%default total

||| `Getter`s allows us to extract exactly one piece of data of type `a` from
||| a source value of type `s`. They are therefore like `Fold`s but with
||| stronger guarantees.
|||
||| Just like `Fold`s and other optics, `Getter`s can be composed sequentially,
||| and just like `Fold`s, `Getter`s have two additional type parameters
||| (`t` and `b`), which have no runtime relevance and are only used to
||| compose them with other optics.
public export
record Getter (s,t,a,b : Type) where
  constructor G
  to_ : s -> a

||| Sequential composition of `Getter`s.
public export %inline
(|>) : Getter s t a b -> Getter a b c d -> Getter s t c d
G f |> G g = G $ g . f
--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting other optics to `Getter`s.
public export
interface ToGetter (0 o : Type -> Type -> Type -> Type -> Type) where
  toGetter : o s t a b -> Getter s t a b

public export %inline
ToGetter Getter where toGetter = id

||| Use a `Getter` to extract a piece of data from a source value.
public export %inline
to : ToGetter o => o s t a b -> s -> a
to = to_ . toGetter

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
ToFold Getter where
  toFold f = F (. to_ f)
