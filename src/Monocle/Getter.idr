module Monocle.Getter

import Monocle.Fold

%default total

public export
record Getter (s,t,a,b : Type) where
  constructor G
  to_ : s -> a

public export %inline
(|>) : Getter s t a b -> Getter a b c d -> Getter s t c d
G f |> G g = G $ g . f
--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface ToGetter (0 o : Type -> Type -> Type -> Type -> Type) where
  toGetter : o s t a b -> Getter s t a b

public export %inline
ToGetter Getter where toGetter = id

public export %inline
to : ToGetter o => o s t a b -> s -> a
to = to_ . toGetter

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
ToFold Getter where
  toFold f = F (. to_ f)
