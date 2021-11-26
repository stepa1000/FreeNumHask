{-# LANGUAGE Arrows #-}

module Control.Free.Algebra.Additive where

import qualified Prelude

import Control.Free.Algebra.Prelude

data FreeAdditive a
  = FAdd a a
  | Zero

instance Functor FreeAdditive where
  fmap f (FAdd a a) = FAdd (f a) (f a)
  fmap _ Zero = Zero

instance Additive (FreeAdditive a) where
  (+) = FAdd
  zero = Zero

mapFreeAdditive' :: Additive b => (a -> b) -> FreeAdditive a -> b
mapFreeAdditive' fa (FAdd a1 a2) = (fa a1) + (fa a2)
mapFreeAdditive' _ Zero = zero

mapFreeAdditiveM' :: (Additive b, Monad m) => (a -> m b) -> FreeAdditive a -> m b
mapFreeAdditiveM' fa (FAdd a1 a2) = do
  b1 <- fa a1
  b2 <- fa a2
  return $ b1 + b2
mapFreeAdditiveM' _ Zero = return zero

proMapFreeAdditive' :: p a b -> A p (FreeAdditive a) b
proMapFreeAdditive' pab = proc fadd -> do
  

data FreeSubtractive a
  = FAdditive (FreeAdditive a)
  | FNegate a
  | FSubtract a a

instance Functor FreeSubtractive where
  fmap f (FAdditive ad) = FAdditive $ fmap f ad
  fmap f (FNegate a) = FNegate (f a)
  fmap f (FSubtract a a) = FSubtract (f a) (f a)

data Subtractive (FreeSubtractive a) where
  negate = FNegate
  (-) = FSubtract

mapFreeSubtractive' :: Subtractive b => (a -> b) -> FreeSubtractive a -> b
mapFreeSubtractive' fa (FAdditive ad) = mapFreeAdditive' ad
mapFreeSubtractive' fa (FNegate a) = negate $ fa a
mapFreeSubtractive' fa (FSubtract a a) = (f a) - (f a)
