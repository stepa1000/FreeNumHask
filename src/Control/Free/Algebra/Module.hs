{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Free.Algebra.Module where

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
import Control.Free.Algebra.Ring

data FreeAdditiveAction a m = ActAdd a m -- ????
newtype FreeActionAdditive m a = FreeActionAdditive
  {unFreeActionAdditive :: FreeAdditiveAction a m}

annihilationFreeAdditiveAction :: FreeAdditiveAction a m -> (a,m)
annihilationFreeAdditiveAction (ActAdd a m) = (a,m)

instance Functor (FreeAdditiveAction a) where
  fmap f (ActAdd a b) = ActAdd a (f b)

instance Foldable (FreeAdditiveAction a) where
  foldMap f (ActAdd fa fb) = f fb

instance Traversable (FreeAdditiveAction a) where
  traverse f (ActAdd fa fb) = ActAdd fa <$> f fb

type FixAdditiveAction a b = FixLetVar b (FreeAdditiveAction a)

instance Additive a => AdditiveAction (FixAdditiveAction a b) a where
  a .+ m = Fix $ LetExp $ Exp $ ActAdd a m
  m +. a = Fix $ LetExp $ Exp $ ActAdd a m

proMapFreeAdditiveAction :: (AdditiveAction mb b, Additive b)
                         => p ma mb
                         -> p a b
                         -> AltArr p (FreeAdditiveAction a ma) mb
proMapFreeAdditiveAction pmamb pab = proc fadd -> do
  b <- arr (uncurry (.+)) <<< liftFree2 pab *** liftFree2 pmamb -< annihilationFreeAdditiveAction fadd
  returnA -< b

proMapFixAdditiveAction :: (AdditiveAction mb b, Additive b)
                        => p ma mb
                        -> p a b
                        -> AltArr p (FixAdditiveAction a ma) mb
proMapFixAdditiveAction pmamb pab = proLetFoldFix pmamb (joinAltArr $
  proMapFreeAdditiveAction id (liftFree2 pab) )

newtype FreeSubtractiveAction a m = FreeSubtractiveAction
  {unFreeSubtractiveAction :: FreeAdditiveAction a m} -- deriving newtype
  deriving (Traversable, Foldable, Functor)

type FixSubtractiveAction a b = FixLetVar b (FreeSubtractiveAction a)

instance Subtractive a => SubtractiveAction (FixSubtractiveAction a b) a where
  a .- m = Fix $ LetExp $ Exp $ FreeSubtractiveAction $ ActAdd a m
  m -. a = Fix $ LetExp $ Exp $ FreeSubtractiveAction $ ActAdd a m

proMapFreeSubtractiveAction :: (SubtractiveAction mb b, Subtractive b)
                         => p ma mb
                         -> p a b
                         -> AltArr p (FreeSubtractiveAction a ma) mb
proMapFreeSubtractiveAction pmamb pab = proc (FreeSubtractiveAction fadd) -> do
  b <- arr (uncurry (.-)) <<< liftFree2 pab *** liftFree2 pmamb -< annihilationFreeAdditiveAction fadd
  returnA -< b

proMapFixSubtractiveAction :: (SubtractiveAction mb b, Subtractive b)
                        => p ma mb
                        -> p a b
                        -> AltArr p (FixSubtractiveAction a ma) mb
proMapFixSubtractiveAction pmamb pab = proLetFoldFix pmamb (joinAltArr $
  proMapFreeSubtractiveAction id (liftFree2 pab) )

proMapFreeAction :: (f a ma -> FreeAdditiveAction a ma)
                 -> (b -> mb -> mb)
                 -> p ma mb
                 -> p a b
                 -> AltArr p (f a ma) mb
proMapFreeAction ann fa pmamb pab = proc fadd -> do
  b <- arr (uncurry fa ) <<< liftFree2 pab *** liftFree2 pmamb -< annihilationFreeAdditiveAction $ ann fadd
  returnA -< b
{-}
proMapFixAction :: (Traversable (f a), Foldable (f a), Functor (f a))
                => (f a ma -> FreeAdditiveAction a ma)
                -> (b -> mb -> mb)
                -> p ma mb
                -> p a b
                -> AltArr p (FixLetVar ma (f a) ) mb
proMapFixAction ann fa pmamb pab = proLetFoldFix pmamb (joinAltArr $
  proMapFreeAction ann fa id (liftFree2 pab) )
-}

newtype FreeMultiplicativeAction a m = FreeMultiplicativeAction
  {unFreeMultiplicativeAction :: FreeAdditiveAction a m} -- deriving newtype
  deriving (Traversable, Foldable, Functor)

type FixMultiplicativeAction a b = FixLetVar b (FreeMultiplicativeAction a)

instance Multiplicative a => MultiplicativeAction (FixMultiplicativeAction a b) a where
  a .* m = Fix $ LetExp $ Exp $ FreeMultiplicativeAction $ ActAdd a m
  m *. a = Fix $ LetExp $ Exp $ FreeMultiplicativeAction $ ActAdd a m

proMapFixMultiplicativeAction :: (MultiplicativeAction mb b, Multiplicative b)
                        => p ma mb
                        -> p a b
                        -> AltArr p (FixMultiplicativeAction a ma) mb
proMapFixMultiplicativeAction pmamb pab = proLetFoldFix pmamb (joinAltArr $
  proMapFreeAction unFreeMultiplicativeAction (.*) id (liftFree2 pab) )

newtype FreeDivisiveAction a m = FreeDivisiveAction
  {unFreeDivisiveAction :: FreeAdditiveAction a m} -- deriving newtype
  deriving (Traversable, Foldable, Functor)

type FixDivisiveAction a b = FixLetVar b (FreeDivisiveAction a)

instance Divisive a => DivisiveAction (FixDivisiveAction a b) a where
  a ./ m = Fix $ LetExp $ Exp $ FreeDivisiveAction $ ActAdd a m
  m /. a = Fix $ LetExp $ Exp $ FreeDivisiveAction $ ActAdd a m

proMapFixDivisiveAction :: (DivisiveAction mb b, Divisive b)
                        => p ma mb
                        -> p a b
                        -> AltArr p (FixDivisiveAction a ma) mb
proMapFixDivisiveAction pmamb pab = proLetFoldFix pmamb (joinAltArr $
  proMapFreeAction unFreeDivisiveAction (./) id (liftFree2 pab) )

data FreeModule a m =
    FModDist (FreeDistributive m)
  | FModMultAct (FreeMultiplicativeAction a m)
  deriving (Traversable, Foldable, Functor)

annihilationFreeModule :: FreeModule a m -> Either (FreeDistributive m) (FreeMultiplicativeAction a m)
annihilationFreeModule (FModDist fd) = Left fd
annihilationFreeModule (FModMultAct fm) = Right fm

newtype FixModule a m = FixModule
  {unFixModule :: FixLetVar m (FreeModule a)}

instance Additive (FixModule a m) where
  (FixModule x :: FixModule a m) + (FixModule y :: FixModule a m) = FixModule v
    where
      v :: FixLetVar m (FreeModule a)
      v = Fix $ LetExp $ Exp $ FModDist $ FDAdd $ FAdd x y
  zero = FixModule $ Fix $ LetExp $ Exp $ FModDist $ FDAdd Zero

instance Multiplicative (FixModule a m) where
  (FixModule x) * (FixModule y) = FixModule $ Fix $ LetExp $ Exp $ FModDist $ FDMult $ Mult x y
  one = FixModule $ Fix $ LetExp $ Exp $ FModDist $ FDMult One

instance Multiplicative a => MultiplicativeAction (FixModule a m) a where
  a .* (FixModule m) = FixModule $ Fix $ LetExp $ Exp $ FModMultAct $ FreeMultiplicativeAction $ ActAdd a m
  (FixModule m) *. a = FixModule $ Fix $ LetExp $ Exp $ FModMultAct $ FreeMultiplicativeAction $ ActAdd a m

proMapFreeModule :: (Module mb b,Distributive mb)
                 => p ma mb
                 -> p a b
                 -> AltArr p (FreeModule a ma) mb
proMapFreeModule pmamb pab = proc aafm -> do
  mb <- id ||| id <<< proMapFreeDistributive pmamb +++ (proMapFreeAction unFreeMultiplicativeAction (.*) pmamb pab)
    -< annihilationFreeModule aafm
  returnA -< mb
