{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}

module Control.Free.Algebra.Ring where

import GHC.Generics

import qualified Prelude
import Prelude (($))

import Control.Free.Algebra.Prelude

import Control.Free.Algebra.Cse
import Control.Free.Algebra.Arrow

import Data.Generics.Traversable
import Data.Foldable
import Control.Applicative

import Control.Free.Algebra.Multiplicative
import Control.Free.Algebra.Additive

data FreeDistributive a =
    FDAdd (FreeAdditive a)
  | FDMult (FreeMultiplicative a)
  deriving (Traversable, Foldable, Functor)

annihilationFreeDistributive :: FreeDistributive a -> Either (FreeAdditive a) (FreeMultiplicative a)
annihilationFreeDistributive (FDAdd fa) = Left fa
annihilationFreeDistributive (FDMult fm) = Right fm

type FixDistributive a = FixLetVar a FreeDistributive

instance Additive (FixDistributive b) where
  x + y = Fix $ LetExp $ Exp $ FDAdd $ FAdd x y
  zero = Fix $ LetExp $ Exp $ FDAdd Zero

instance Multiplicative (FixDistributive b) where
  x * y = Fix $ LetExp $ Exp $ FDMult $ Mult x y
  one = Fix $ LetExp $ Exp $ FDMult One

proMapFreeDistributive :: Distributive b
                       => p a b
                       -> AltArr p (FreeDistributive a) b
proMapFreeDistributive pab = proc fadd -> do
  b <- id ||| id <<< proMapFreeAdditive' pab +++ proMapFreeMultiplicative pab
    -< annihilationFreeDistributive fadd
  returnA -< b

proMapFixDistributive :: Distributive b
                       => p a b
                       -> AltArr p (FixDistributive a) b
proMapFixDistributive pab = proLetFoldFix pab (joinAltArr $ proMapFreeDistributive id)
