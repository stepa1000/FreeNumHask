{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Free.Algebra.Additive where

import GHC.Generics

import qualified Prelude
import Prelude (($))

import Control.Free.Algebra.Prelude

import Control.Free.Algebra.Cse
import Control.Free.Algebra.Arrow

import Data.Generics.Traversable
import Data.Foldable
import Control.Applicative

data FreeAdditive a
  = FAdd a a
  | Zero

annihilationFreeAdditive :: FreeAdditive a -> Either (a,a) () -- GENERIC!!!!!!!!!!!!!
annihilationFreeAdditive (FAdd a b) = Left (a,b)
annihilationFreeAdditive Zero = Right ()

instance Functor FreeAdditive where
  fmap f (FAdd a b) = FAdd (f a) (f b)
  fmap _ Zero = Zero
{-}
instance (Generic (FreeAdditive a)) => GTraversable c (FreeAdditive a)

instance (Generic (FreeAdditive a), GTraversable c (FreeAdditive a)) => Foldable FreeAdditive where
  foldMap = gfoldMap

instance (Generic (FreeAdditive a), GTraversable c (FreeAdditive a)) => Traversable FreeAdditive where
  traverse = gtraverse
-}

instance Foldable FreeAdditive where
  foldMap f (FAdd fa fb) = f fa <> f fb
  foldMap f Zero = mempty

instance Traversable FreeAdditive where
  traverse f (FAdd fa fb) = liftA2 FAdd (f fa) (f fb)
  traverse _ Zero = pure $ Zero

type FixAdditive b = FixLetVar b FreeAdditive

instance Additive (FixAdditive b) where
  x + y = Fix $ LetExp $ Exp $ FAdd x y
  zero = Fix $ LetExp $ Exp Zero

mapFreeAdditive' :: Additive b => (a -> b) -> FreeAdditive a -> b
mapFreeAdditive' fa (FAdd a1 a2) = (fa a1) + (fa a2)
mapFreeAdditive' _ Zero = zero

mapFreeAdditiveM' :: (Additive b, Monad m) => (a -> m b) -> FreeAdditive a -> m b
mapFreeAdditiveM' fa (FAdd a1 a2) = do
  b1 <- fa a1
  b2 <- fa a2
  return $ b1 + b2
mapFreeAdditiveM' _ Zero = return zero

proMapFreeAdditive' :: Additive b => p a b -> AltArr p (FreeAdditive a) b
proMapFreeAdditive' pab = proc fadd -> do
  b <- id ||| id <<< gadd +++ gz -< annihilationFreeAdditive fadd
  returnA -< b
  where
    gadd = proc (x',y') -> do
      x <- liftFree2 pab -< x'
      y <- liftFree2 pab -< y'
      returnA -< x + y
    gz = proc _ -> returnA -< zero

proMapFixAdditive :: Additive b => p a b -> AltArr p (FixAdditive a) b
proMapFixAdditive pab = proLetFoldFix pab (joinAltArr $ proMapFreeAdditive' id)

data FreeSubtractive a
  = FAdditive (FreeAdditive a)
  | FNegate a
  | FSubtract a a

annihilationFreeSubtractive :: FreeSubtractive a
                            -> Either (FreeAdditive a) (Either a (a,a))
annihilationFreeSubtractive (FAdditive fa) = Left fa
annihilationFreeSubtractive (FNegate a) = Right $ Left a
annihilationFreeSubtractive (FSubtract a b) = Right $ Right (a,b)

instance Functor FreeSubtractive where
  fmap f (FAdditive ad) = FAdditive $ fmap f ad
  fmap f (FNegate a) = FNegate (f a)
  fmap f (FSubtract a b) = FSubtract (f a) (f b)
{-}
instance (Generic (FreeSubtractive a), GTraversable c (FreeSubtractive a)) => Foldable FreeSubtractive where
  foldMap = gfoldMap

instance (Generic (FreeSubtractive a), GTraversable c (FreeSubtractive a)) => Traversable FreeSubtractive where
  traverse = gtraverse
-}

instance Foldable FreeSubtractive where
  foldMap f (FAdditive fb) = foldMap f fb
  foldMap f (FNegate fb) = f fb
  foldMap f (FSubtract fa fb) = (f fa) <> (f fb)

instance Traversable FreeSubtractive where
  traverse f (FSubtract fa fb) = liftA2 FSubtract (f fa) (f fb)
  traverse f (FAdditive fb) = FAdditive <$> traverse f fb
  traverse f (FNegate fb) = FNegate <$> f fb

type FixSubtractive b = FixLetVar b FreeSubtractive

instance Additive (FixSubtractive a) where
  x + y = Fix $ LetExp $ Exp $ FAdditive $ FAdd x y
  zero = Fix $ LetExp $ Exp $ FAdditive Zero

instance Subtractive (FixSubtractive a) where
  negate = Fix . LetExp . Exp . FNegate
  x - y = Fix $ LetExp $ Exp $ FSubtract x y

proMapFixSubtractive :: Subtractive b => p a b -> AltArr p (FixSubtractive a) b
proMapFixSubtractive pab = proLetFoldFix pab (joinAltArr $ proMapFreeSubtractive' id)

mapFreeSubtractive' :: Subtractive b => (a -> b) -> FreeSubtractive a -> b
mapFreeSubtractive' fa (FAdditive ad) = mapFreeAdditive' fa ad
mapFreeSubtractive' fa (FNegate a) = negate $ fa a
mapFreeSubtractive' fa (FSubtract a b) = (fa a) - (fa b)

proMapFreeSubtractive' :: Subtractive b => p a b -> AltArr p (FreeSubtractive a) b
proMapFreeSubtractive' pab = proc fs -> do
  b <- id ||| (id ||| id) <<< proMapFreeAdditive' pab +++ (ne +++ su) -< annihilationFreeSubtractive fs
  returnA -< b
  where
    ne = proc a -> do
      b <- liftFree2 pab -< a
      returnA -< negate b
    su = proc (x',y') -> do
      x <- liftFree2 pab -< x'
      y <- liftFree2 pab -< y'
      returnA -< x - y
