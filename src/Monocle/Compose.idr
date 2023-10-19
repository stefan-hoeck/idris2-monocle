module Monocle.Compose

import Monocle.Fold
import Monocle.Getter
import Monocle.Iso
import Monocle.Lens
import Monocle.Optional
import Monocle.Prism
import Monocle.Setter
import Monocle.Traversal

%default total

||| Interface for the sequencing of different types of optics.
|||
||| The kind of optic we get as a result is determined by the kinds of optics
||| we sequence. For instance, sequencing a Lens with a Prism results in
||| an Optional, while sequencing with an Iso does preserve an optic's type.
public export
interface OSeq (0 k,l,m : Type -> Type -> Type -> Type -> Type) | k,l where
  seq : k s t a b -> l a b c d -> m s t c d

infixl 9 .>

public export %inline
(.>) : {0 k,l,m : _} -> k s t a b -> l a b c d -> OSeq k l m => m s t c d
f .> g = seq f g

public export %inline
OSeq Iso Iso Iso where seq = (|>)

public export %inline
OSeq Iso Lens Lens where seq x y = toLens x |> y

public export %inline
OSeq Iso Prism Prism where seq x y = toPrism x |> y

public export %inline
OSeq Iso Optional Optional where seq x y = toOptional x |> y

public export %inline
OSeq Iso Traversal Traversal where seq x y = toTraversal x |> y

public export %inline
OSeq Iso Getter Getter where seq x y = toGetter x |> y

public export %inline
OSeq Iso Setter Setter where seq x y = toSetter x |> y

public export %inline
OSeq Iso Fold Fold where seq x y = toFold x |> y

public export %inline
OSeq Lens Lens Lens where seq = (|>)

public export %inline
OSeq Lens Iso Lens where seq x y = x |> toLens y

public export %inline
OSeq Lens Prism Optional where seq x y = toOptional x |> toOptional y

public export %inline
OSeq Lens Optional Optional where seq x y = toOptional x |> y

public export %inline
OSeq Lens Traversal Traversal where seq x y = toTraversal x |> y

public export %inline
OSeq Lens Getter Getter where seq x y = toGetter x |> y

public export %inline
OSeq Lens Setter Setter where seq x y = toSetter x |> y

public export %inline
OSeq Lens Fold Fold where seq x y = toFold x |> y

public export %inline
OSeq Prism Prism Prism where seq = (|>)

public export %inline
OSeq Prism Iso Prism where seq x y = x |> toPrism y

public export %inline
OSeq Prism Lens Optional where seq x y = toOptional x |> toOptional y

public export %inline
OSeq Prism Optional Optional where seq x y = toOptional x |> y

public export %inline
OSeq Prism Traversal Traversal where seq x y = toTraversal x |> y

public export %inline
OSeq Prism Getter Fold where seq x y = toFold x |> toFold y

public export %inline
OSeq Prism Setter Setter where seq x y = toSetter x |> y

public export %inline
OSeq Prism Fold Fold where seq x y = toFold x |> y

public export %inline
OSeq Optional Optional Optional where seq = (|>)

public export %inline
OSeq Optional Iso Optional where seq x y = x |> toOptional y

public export %inline
OSeq Optional Lens Optional where seq x y = x |> toOptional y

public export %inline
OSeq Optional Prism Optional where seq x y = x |> toOptional y

public export %inline
OSeq Optional Traversal Traversal where seq x y = toTraversal x |> y

public export %inline
OSeq Optional Getter Fold where seq x y = toFold x |> toFold y

public export %inline
OSeq Optional Setter Setter where seq x y = toSetter x |> y

public export %inline
OSeq Optional Fold Fold where seq x y = toFold x |> y

public export %inline
OSeq Traversal Traversal Traversal where seq = (|>)

public export %inline
OSeq Traversal Iso Traversal where seq x y = x |> toTraversal y

public export %inline
OSeq Traversal Lens Traversal where seq x y = x |> toTraversal y

public export %inline
OSeq Traversal Prism Traversal where seq x y = x |> toTraversal y

public export %inline
OSeq Traversal Optional Traversal where seq x y = x |> toTraversal y

public export %inline
OSeq Traversal Getter Fold where seq x y = toFold x |> toFold y

public export %inline
OSeq Traversal Setter Setter where seq x y = toSetter x |> y

public export %inline
OSeq Traversal Fold Fold where seq x y = toFold x |> y

public export %inline
OSeq Setter Setter Setter where seq = (|>)

public export %inline
OSeq Setter Iso Setter where seq x y = x |> toSetter y

public export %inline
OSeq Setter Lens Setter where seq x y = x |> toSetter y

public export %inline
OSeq Setter Prism Setter where seq x y = x |> toSetter y

public export %inline
OSeq Setter Optional Setter where seq x y = x |> toSetter y

public export %inline
OSeq Setter Traversal Setter where seq x y = x |> toSetter y

public export %inline
OSeq Getter Getter Getter where seq = (|>)

public export %inline
OSeq Getter Iso Getter where seq x y = x |> toGetter y

public export %inline
OSeq Getter Lens Getter where seq x y = x |> toGetter y

public export %inline
OSeq Getter Prism Fold where seq x y = toFold x |> toFold y

public export %inline
OSeq Getter Optional Fold where seq x y = toFold x |> toFold y

public export %inline
OSeq Getter Traversal Fold where seq x y = toFold x |> toFold y

public export %inline
OSeq Getter Fold Fold where seq x y = toFold x |> y

public export %inline
OSeq Fold Fold Fold where seq = (|>)

public export %inline
OSeq Fold Iso Fold where seq x y = x |> toFold y

public export %inline
OSeq Fold Lens Fold where seq x y = x |> toFold y

public export %inline
OSeq Fold Prism Fold where seq x y = x |> toFold y

public export %inline
OSeq Fold Optional Fold where seq x y = x |> toFold y

public export %inline
OSeq Fold Traversal Fold where seq x y = x |> toFold y

public export %inline
OSeq Fold Getter Fold where seq x y = x |> toFold y

export
atO : Eq k => k -> Optional' (List (k,v)) v
atO key = eqFirst key fst .> snd
