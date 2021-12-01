{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Free.Algebra.Multiplicative where

import GHC.Generics

import qualified Prelude
import Prelude (($))

import Control.Free.Algebra.Prelude

import Control.Free.Algebra.Cse
import Control.Free.Algebra.Arrow

import Data.Generics.Traversable
import Data.Foldable
import Control.Applicative

data FreeMultiplicative a =
    Mult a a
  | One

annihilationFreeMultiplicative :: FreeMultiplicative a -> Either (a,a) ()
annihilationFreeMultiplicative (Mult a b) = Left (a,b)
annihilationFreeMultiplicative One = Right ()

instance Functor FreeMultiplicative where
  fmap f (Mult a b) = Mult (f a) (f b)
  fmap _ One = One

instance Foldable FreeMultiplicative where
  foldMap f (Mult fa fb) = f fa <> f fb
  foldMap f One = mempty

instance Traversable FreeMultiplicative where
  traverse f (Mult fa fb) = liftA2 Mult (f fa) (f fb)
  traverse _ One = pure $ One

type FixMultiplicative b = FixLetVar b FreeMultiplicative

instance Multiplicative (FixMultiplicative b) where
  x * y = Fix $ LetExp $ Exp $ Mult x y
  one = Fix $ LetExp $ Exp One

proMapFreeMultiplicative :: Multiplicative b
                         => p a b
                         -> AltArr p (FreeMultiplicative a) b
proMapFreeMultiplicative pab = proc fadd -> do
  b <- id ||| id <<< gadd +++ gz -< annihilationFreeMultiplicative fadd
  returnA -< b
  where
    gadd = proc (x',y') -> do
      x <- liftFree2 pab -< x'
      y <- liftFree2 pab -< y'
      returnA -< x * y
    gz = proc _ -> returnA -< one

proMapFixMultiplicative :: Multiplicative b => p a b -> AltArr p (FixMultiplicative a) b
proMapFixMultiplicative pab = proLetFoldFix pab (joinAltArr $ proMapFreeMultiplicative id)

data FreeDivisive f a =
    Recip a
  | FMult (f a)

annihilationFreeDivisive :: FreeDivisive f a -> Either a (f a)
annihilationFreeDivisive (Recip a) = Left a
annihilationFreeDivisive (FMult fa) = Right $ fa

instance Functor f => Functor (FreeDivisive f) where
  fmap f (Recip a) = Recip (f a)
  fmap f (FMult a) = FMult (fmap f a)

instance Foldable f => Foldable (FreeDivisive f) where
  foldMap f (Recip fa) = f fa
  foldMap f (FMult fa) = foldMap f fa

instance Traversable f => Traversable (FreeDivisive f) where
  traverse f (Recip fa) = Recip <$> (f fa)
  traverse f (FMult fa) = FMult <$> (traverse f fa)

type FixDivisive f a = FixLetVar a (FreeDivisive f)

instance Divisive (FixDivisive FreeMultiplicative a) where
  recip = Fix . LetExp . Exp . Recip

instance Multiplicative (FixDivisive FreeMultiplicative a) where
  x * y = Fix $ LetExp $ Exp $ FMult $ Mult x y
  one = Fix $ LetExp $ Exp $ FMult One

proMapFreeDivisive :: (Divisive b, Multiplicative b)
                   => p a b
                   -> AltArr p (f a) b
                   -> AltArr p (FreeDivisive f a) b
proMapFreeDivisive pab pfab = proc fadd -> do
  b <- id ||| id <<< gadd +++ pfab -< annihilationFreeDivisive fadd
  returnA -< b
  where
    gadd = proc x' -> do
      x <- liftFree2 pab -< x'
      returnA -< recip x

proMapFixDivisive :: Divisive b => p a b -> AltArr p (FixDivisive FreeMultiplicative a) b
proMapFixDivisive pab = proLetFoldFix pab (joinAltArr $
  proMapFreeDivisive id (proMapFreeMultiplicative id) )
