module Monocle.Lens

import Monocle.Fold
import Monocle.Getter
import Monocle.Optional
import Monocle.Setter
import Monocle.Traversal
import Control.Monad.State
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

||| A Lens unifies a `Setter` and a Getter, and is therefore typically used
||| to focus on a single value in a larger data type.
|||
||| Lenses are best known for allowing us to extract and update record fields,
||| but they can also be used with other types of data.
|||
||| A Lens is parameterized over four parameters, because in general
||| we could not only update a value but also its type with an updating
||| function. Consider Lens `fst`, where `s` corresponds to `(a,c)` and
||| `t` corresponds to `(b,c)`. Accordingly, if we have a function from
||| `a` to `b`, we can convert a pair of type `(a,c)` to one of type `(b,c)`.
public export
record Lens (s,t,a,b : Type) where
  constructor L
  get_ : s -> a
  mod_ : (a -> b) -> s -> t

||| Convenience alias for monomorphic lenses, which do not allow
||| us to change the value and source types.
public export
0 Lens' : (s,a : Type) -> Type
Lens' s a = Lens s s a a

||| Alternative constructor for creating a Lens from a getting and
||| a setting function.
public export
lens : (s -> a) -> (b -> s -> t) -> Lens s t a b
lens f g = L f $ \h,v => g (h $ f v) v

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting other optics to lenses.
public export
interface ToLens (0 o : Type -> Type -> Type -> Type -> Type) where
  toLens : o s t a b -> Lens s t a b

public export %inline
ToLens Lens where toLens = id

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Specialized version of `set` that sometimes helps with type inference.
public export %inline
setL : Lens s t a b -> b -> s -> t
setL l = mod_ l . const

||| Modify the value focussed on by the given Lens with an effectful
||| computation.
public export %inline
modF : Functor f => Lens s t a b -> (a -> f b) -> s -> f t
modF l g v = (\x => setL l x v) <$> g (get_ l v)

||| Sequential composition of lenses.
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
  toOptional l = O (Right . l.get_) l.mod_

public export %inline
ToSetter Lens where
  toSetter = S . mod_

public export %inline
ToTraversal Lens where
  toTraversal l = T (modF l) (toFold l) (toSetter l)

--------------------------------------------------------------------------------
--          Lenses
--------------------------------------------------------------------------------

||| A Lens focussing on the first element of a pair.
public export %inline
fst : Lens (a,c) (b,c) a b
fst = L fst mapFst

||| A Lens focussing on the second element of a pair.
public export
snd : Lens (c,a) (c,b) a b
snd = L snd mapSnd

||| A Lens focussing on the head of a non-empty vector.
public export
head : Lens' (Vect (S n) a) a
head = lens head $ \x,v => x :: tail v

||| A Lens focussing on the tail of a non-empty vector.
public export
tail : Lens' (Vect (S n) a) (Vect n a)
tail = lens tail $ \x,v => head v :: x

||| A Lens focussing on a specific element in a vector.
public export
ix : Fin n -> Lens' (Vect n a) a
ix x = L (index x) (updateAt x)

||| A Lens focussing on the head of a non-empty list.
public export
head1 : Lens' (List1 a) a
head1 = lens head $ \x,v => x ::: tail v

||| A Lens focussing on the tail of a non-empty list.
public export
tail1 : Lens' (List1 a) (List a)
tail1 = lens tail $ \x,v => head v ::: x

||| A Lens focussing on the value associated with the given
||| key in a `SortedMap`.
|||
||| Note: Unlike a related `Optional`, which we get via `at k .> just`,
|||       this Lens allows us to remove a key from a dictionary by
|||       setting the corresponding value to `Nothing`.
public export
at : Ord k => k -> Lens' (SortedMap k v) (Maybe v)
at x = lens (lookup x) $ \mv,m => maybe (delete x m) (\v => insert x v m) mv

||| Like `at` but yields the given default value in case no
||| value has been associated with the given key.
export
atDflt : Ord k => k -> v -> Lens' (SortedMap k v) v
atDflt x v = lens (fromMaybe v . lookup x) (insert x)

||| Like `atDflt` but using an auto-implicit argument for the default
||| value.
export %inline
atAuto : Ord k => k -> {auto prf : v} -> Lens' (SortedMap k v) v
atAuto x = atDflt x prf

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

||| Lens focussing on a single element in a heterogeneous list.
public export
prod :
     {0 ks : List k}
  -> {0 f  : k -> Type}
  -> (0 t : k)
  -> {auto e : Elem t ks}
  -> Lens' (All f ks) (f t)
prod t = L allGet allUpd

public export
allHead : Lens' (All f (k::ks)) (f k)
allHead = lens (\(v::_) => v) (\v,(_::vs) => v::vs)

public export
allTail : Lens' (All f (k::ks)) (All f ks)
allTail = lens (\(_::vs) => vs) (\vs,(v::_) => v::vs)

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

||| View a state through a lens
export
stL : Functor m => Lens' t s -> StateT s m x -> StateT t m x
stL l (ST f) = ST $ \v => (\(w,r) => (setL l w v, r)) <$> f (l.get_ v)

-- ||| View a stateful computation resulting in a monoid through an
-- ||| optional.
-- export
-- stateO : Monoid x => Optional' t s -> State s x -> State t x
-- stateO o (ST f) =
--   ST $ \v => case first o v of
--     Nothing  => Id (v, neutral)
--     Just vs  => let Id (vs2,w) := f vs in Id (set o vs2 v, w)
--
