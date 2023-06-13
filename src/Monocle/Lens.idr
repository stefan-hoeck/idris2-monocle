module Monocle.Lens

import Monocle.Fold
import Monocle.Getter
import Monocle.Optional
import Monocle.Setter
import Monocle.Traversal
import Data.List.Quantifiers.Extra
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.Vect

%default total

infixl 9 |>

--------------------------------------------------------------------------------
--          Lens
--------------------------------------------------------------------------------

public export
record Lens (s,t,a,b : Type) where
  constructor L
  get_ : s -> a
  mod_ : (a -> b) -> s -> t

public export
0 Lens' : (s,a : Type) -> Type
Lens' s a = Lens s s a a

public export
lens : (s -> a) -> (b -> s -> t) -> Lens s t a b
lens f g = L f $ \h,v => g (h $ f v) v

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface ToLens (0 o : Type -> Type -> Type -> Type -> Type) where
  toLens : o s t a b -> Lens s t a b

public export %inline
ToLens Lens where toLens = id

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
setL : Lens s t a b -> b -> s -> t
setL l = mod_ l . const

public export %inline
modF : Functor f => Lens s t a b -> (a -> f b) -> s -> f t
modF l g v = (\x => setL l x v) <$> g (get_ l v)

public export
(|>) : Lens s t x y -> Lens x y a b -> Lens s t a b
L g1 s1 |> L g2 s2 = L (g2 . g1) (s1 . s2)

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
ToGetter Lens where
  toGetter  = G . get_

public export %inline
ToFold Lens where
  toFold = toFold . toGetter

public export
ToOptional Lens where
  toOptional l = O (Right . l.get_) (setL l)

public export %inline
ToTraversal Lens where
  toTraversal l = T (modF l)

public export %inline
ToSetter Lens where
  toSetter = S . mod_

--------------------------------------------------------------------------------
--          Lenses
--------------------------------------------------------------------------------

public export %inline
fst : Lens (a,c) (b,c) a b
fst = L fst mapFst

public export
snd : Lens (c,a) (c,b) a b
snd = L snd mapSnd

public export
head : Lens' (Vect (S n) a) a
head = lens head $ \x,v => x :: tail v

public export
tail : Lens' (Vect (S n) a) (Vect n a)
tail = lens tail $ \x,v => head v :: x

public export
head1 : Lens' (List1 a) a
head1 = lens head $ \x,v => x ::: tail v

public export
tail1 : Lens' (List1 a) (List a)
tail1 = lens tail $ \x,v => head v ::: x

public export
at : Ord k => k -> Lens' (SortedMap k v) (Maybe v)
at x = lens (lookup x) $ \mv,m => maybe (delete x m) (\v => insert x v m) mv

public export
allGet :
     {0 ks : List k}
  -> {0 f  : k -> Type}
  -> {auto e : Elem t ks}
  -> All f ks
  -> f t
allGet @{Here}    (h::_)  = h
allGet @{There _} (_::vs) = allGet vs

public export
allUpd :
     {0 ks : List k}
  -> {0 f  : k -> Type}
  -> {auto e : Elem t ks}
  -> (f t -> f t)
  -> All f ks
  -> All f ks
allUpd @{Here}    g (h::vs) = g h :: vs
allUpd @{There _} g (h::vs) = h :: allUpd g vs

public export
prod :
     {0 ks : List k}
  -> {0 f  : k -> Type}
  -> (0 t : k)
  -> {auto e : Elem t ks}
  -> Lens' (All f ks) (f t)
prod t = L allGet allUpd
