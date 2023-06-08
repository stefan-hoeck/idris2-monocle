module Control.Lens.Iso

import Control.Lens.Fold
import Control.Lens.Getter
import Control.Lens.Lens
import Control.Lens.Optional
import Control.Lens.Prism
import Control.Lens.Setter
import Control.Lens.Traversal
import Data.List.Quantifiers
import Data.Maybe

%default total

public export
record Iso s t a b where
  constructor I
  get        : s -> a
  reverseGet : b -> t

public export
0 Iso' : (s,a : Type) -> Type
Iso' s a = Iso s s a a

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export
toO : Iso s t a b -> Optional s t a b
toO (I g r) = O (Right . g) (const . r)

public export
toS : Iso s t a b -> Setter s t a b
toS (I g r) = S $ \f => r . f . g

public export %inline
toF : Iso s t a b -> Fold s a
toF (I g r) = F (. g)

public export
toG : Iso s t a b -> Getter s a
toG (I g r) = G g

public export
toT : Iso s t a b -> Traversal s t a b
toT (I g r) = T $ \f,v => r <$> f (g v)

public export %inline
toL : Iso s t a b -> Lens s t a b
toL (I g r) = L g $ \f => r . f . g

--------------------------------------------------------------------------------
--          Utilitis
--------------------------------------------------------------------------------

public export
rev : Iso s t a b -> Iso b a t s
rev (I f g) = I g f

public export
(>>>) : Iso s t a b -> Iso a b c d -> Iso s t c d
I f1 g1 >>> I f2 g2 = I (f2 . f1) (g1 . g2)

--------------------------------------------------------------------------------
--          Isomorphisms
--------------------------------------------------------------------------------

export
pack : Iso' (List Char) String
pack = I pack unpack

export
unpack : Iso' String (List Char)
unpack = I unpack pack

export
chips : Iso (SnocList a) (SnocList b) (List a) (List b)
chips = I (<>> []) ([<] <><)

export
fish : Iso (List a) (List b) (SnocList a) (SnocList b)
fish = I ([<] <><) (<>> [])

export
swap : Iso (a,b) (c,d) (b,a) (d,c)
swap = I swap swap

export
flip : Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flip = I flip flip

export
uncurry : Iso (a -> b -> c) (d -> e -> f) ((a,b) -> c) ((d,e) -> f)
uncurry = I uncurry curry

export
curry : Iso ((a,b) -> c) ((d,e) -> f) (a -> b -> c) (d -> e -> f)
curry = I curry uncurry

export
swapE : Iso (Either a b) (Either c d) (Either b a) (Either d c)
swapE = I (either Right Left) (either Right Left)

export
withDefault : a -> Iso' (Maybe a) a
withDefault v = I (fromMaybe v) Just

export
leftVoid : Iso (Either Void a) (Either Void b) a b
leftVoid = I (either absurd id) Right

export
rightVoid : Iso (Either a Void) (Either b Void) a b
rightVoid = I (either id absurd) Left

export
any1 : Iso (Any f [a]) (Any g [b]) (f a) (g b)
any1 = I (\case Here v => v) Here
