{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
--{-# LANGUAGE CPP                 #-}

module Control.Free.Algebra.Arrow where

import qualified Prelude

import Control.Free.Algebra.Prelude

import Data.Semigroup as SG

eitherToMT :: Either a b -> (Maybe a,Maybe b)
eitherToMT (Right c) = (Nothing, Just c)
eitherToMT (Left c) = (Just c,Nothing)

mtToEither :: (Maybe a,Maybe b) -> Either a b
mtToEither (_,Just b) = Right b
mtToEither (Just a,_) = Left a

newtype ProArrow p a b = ProArrow
  {runProArrow :: Queue (Sum (->) p) a b}

instance Category (ProArrow p a b) where
  id = ProArrow NilQ
  ProArrow a . ProArrow b = ProArrow $ a . b

instance ( Profunctor p
         , Strong p
         )
         => Arrow (ProArrow p a b) where
  arr bc = ProArrow $ ConsQ (L2 bc) NilQ
  first (ProArrow bc) = ProArrow $ zipWithQ first' bc id

{-}
pseudoArrEither :: Arr f a b -> Arr f c d -> FreeMapping (Arr f) (Either a c) (Either b d)
pseudoArrEither al ar = proc eac -> do
  mm <- *** ( ar . arr fu ) -< eitherToMT eac
  where
    fu (Just a) = a
    fu Nothing = undefined
-}
--import Data.Bifunctor as Bi
{-}
newtype AltArr p a b = (Profunctor p, Choice p) => AltArr
  {unAltArr :: Arr p a b}
  deriving ()
-}
{-}
instance ( Profunctor p
         , Choice p
         )
         => ArrowChoice (Arr p) where
  left ab =
-}
{-}
{-}
newtype AA f a b = AA
  {runAA :: forall r. (Arrow r,ArrowChoice r)
         => (forall x y. f x y -> r x y)
         -> r a b
  }

instance Category (AA f) where
  id = AA (\_ -> id)
  AA f . AA g = AA $ \k -> f k . g k

instance Semigroup (AA f o o) where
    f <> g = f . g

instance Monoid (AA f o o) where
    mempty = id
    mappend = (<>)

instance Arrow (AA f) where
  arr f = AA (\_ -> (arr f))
  AA f *** AA g  = AA $ \k -> f k *** g k
  first  (AA f)  = AA $ \k -> first (f k)
  second (AA f)  = AA $ \k -> second (f k)

instance ArrowChoice (AA f) where
  left (AA f) = AA $ \k -> left (f k)
  right (AA f) = AA $ \k -> right (f k)
  AA f +++ AA g = AA $ \k -> f k +++ g k
  AA f ||| AA g = AA $ \k -> f k ||| g k

type instance AlgebraType0 AA f = ()
type instance AlgebraType  AA c = (Arrow c,ArrowChoice c)

instance FreeAlgebra2 AA where
  liftFree2 = \fab -> AA $ \k -> k fab
  {-# INLINE liftFree2 #-}

  foldNatFree2 fun (AA f) = f fun
  {-# INLINE foldNatFree2 #-}

  codom2  = Proof
  forget2 = Proof
-}

data AltArr f a b where
  AId    :: AltArr f a a
  ACons  :: f b c     -> Queue (AltArr f) a b -> AltArr f a c
  AArr   :: (b -> c)  -> AltArr f a b -> AltArr f a c
  AProd  :: AltArr f a b -> AltArr f a c -> AltArr f a (b, c)
  ASum   :: AltArr f a c -> AltArr f d c -> AltArr f (Either a d) c

arrAltArr :: (b -> c) -> AltArr f b c
arrAltArr f = AArr f AId

foldAltArr :: forall f arr a b. (Arrow arr, ArrowChoice arr)
           => (forall x y. f x y -> arr x y) -> AltArr f a b -> arr a b
foldAltArr _   AId = id
foldAltArr fun (ACons bc ab) = fun bc . foldNatQ (foldNatFree2 fun) ab
foldAltArr fun (AArr f g)    = arr f  . foldNatFree2 fun g
foldAltArr fun (AProd f g)   = foldNatFree2 fun f &&& foldNatFree2 fun g
foldAltArr f (ASum aa1 aa2)  = foldAltArr f aa1 ||| foldAltArr f aa2

instance Category (AltArr f :: Type -> Type -> Type) where
  id = AId
  AId . f = f
  f . AId = f
  (ACons f g) . h  = ACons f (g `snocQ` h)
  (AArr f g)  . h  = AArr f (g . h)
  (AProd f g) . h  = AProd (f . h) (g . h)
  (ASum f g :: AltArr f (Either a d) c) . (h :: AltArr f b (Either a d)) = ACons (ASum f g) (ConsQ h NilQ)   --(f . arr Left . h) (g . arr Right . h)

instance Arrow (AltArr f) where
  arr       = arrAltArr
  first bc  = AProd (bc . arr fst) (arr snd)
  second bc = AProd (arr fst) (bc . arr snd)
  ab *** xy = AProd (ab . arr fst) (xy . arr snd)
  (&&&)     = AProd

instance ArrowChoice (AltArr f) where
  (|||) = ASum
  left bc = ASum (arr Left . bc) (arr Right)
  right bc = ASum (arr Left) (arr Right . bc)
  ac +++ bc = ASum (arr Left . ac) (arr Right . bc)

type instance AlgebraType0 AltArr f = ()
type instance AlgebraType  AltArr c = (Arrow c,ArrowChoice c)

instance FreeAlgebra2 AltArr where
  liftFree2 = \fab -> ACons fab NilQ
  foldNatFree2 = foldAltArr
  codom2  = Proof
  forget2 = Proof

instance Semigroup (AltArr f o o) where
  f <> g = f . g

instance Monoid (AltArr f o o) where
    mempty = AId
    mappend = (<>)
-}
