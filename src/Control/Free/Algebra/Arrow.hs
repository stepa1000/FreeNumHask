{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Arrows #-}
--{-# LANGUAGE CPP                 #-}

module Control.Free.Algebra.Arrow where

import qualified Prelude
import Prelude (const)

import Control.Free.Algebra.Prelude
import Data.Profunctor.Traversing

import Data.Semigroup as SG

--import Data.Bifunctor as Bi

data AltArr f a b where
  AId    :: AltArr f a a
  ACons  :: f b c     -> Queue (AltArr f) a b -> AltArr f a c
  AArr   :: (b -> c)  -> AltArr f a b -> AltArr f a c
  AProd  :: AltArr f a b -> AltArr f a c -> AltArr f a (b, c)
  ASum   :: AltArr f x (Either a d) -> AltArr f a c -> AltArr f d c -> AltArr f x c
  AApp   :: AltArr f x (AltArr f b c,b) -> AltArr f x c -- ????

arrAltArr :: (b -> c) -> AltArr f b c
arrAltArr f = AArr f AId

foldAltArr :: forall f arr a b. (Arrow arr, ArrowChoice arr, ArrowApply arr)
           => (forall x y. f x y -> arr x y) -> AltArr f a b -> arr a b
foldAltArr _   AId = id
foldAltArr fun (ACons bc ab) = fun bc . foldNatQ (foldNatFree2 fun) ab
foldAltArr fun (AArr f g)    = arr f  . foldNatFree2 fun g
foldAltArr fun (AProd f g)   = foldNatFree2 fun f &&& foldNatFree2 fun g
foldAltArr f (ASum fx aa1 aa2)  = foldAltArr f aa1 ||| foldAltArr f aa2 <<< foldAltArr f fx
foldAltArr f (AApp ff) = foldAltArr f ff >>> first (arr (foldAltArr f) ) >>> app

joinAltArr :: AltArr (AltArr f) a b -> AltArr f a b
joinAltArr = foldNatFree2 id
{-}
joinAltArr :: AltArr (AltArr f) a b -> AltArr f a b
joinAltArr AId = AId
joinAltArr (ACons (fbc :: AltArr f b c) (qaa :: Queue (AltArr (AltArr f)) a b ) )
  = ACons fbc (foldNatQ (f . joinAltArr) qaa :: Queue (AltArr f) a c)
  where
    f :: AltArr f x y -> Queue (AltArr f) x y
    f x = ConsQ x NilQ
joinAltArr (AArr bc aa) = AArr bc (joinAltArr aa)
joinAltArr (AProd aa1 aa2) = AProd (joinAltArr aa1) (joinAltArr aa2)
joinAltArr (ASum fxeab fac fdc) = ASum (joinAltArr fxeab) (joinAltArr fac) (joinAltArr fdc)
-}
instance Category (AltArr f :: Type -> Type -> Type) where
  id = AId
  AId . f = f
  f . AId = f
  (ACons f g) . h  = ACons f (g `snocQ` h)
  (AArr f g)  . h  = AArr f (g . h)
  (AProd f g) . h  = AProd (f . h) (g . h)
  (ASum fx f g) . h
    = ASum (fx . h) f g   --(f . arr Left . h) (g . arr Right . h)
  (AApp a) . h = AApp (h >>> a )

instance Arrow (AltArr f) where
  arr       = arrAltArr
  first bc  = AProd (bc . arr fst) (arr snd)
  second bc = AProd (arr fst) (bc . arr snd)
  ab *** xy = AProd (ab . arr fst) (xy . arr snd)
  (&&&)     = AProd

instance ArrowChoice (AltArr f) where
  (|||) = ASum id
  left bc = ASum id (arr Left . bc) (arr Right)
  right bc = ASum id (arr Left) (arr Right . bc)
  ac +++ bc = ASum id (arr Left . ac) (arr Right . bc)

instance ArrowApply (AltArr f) where
  app = AApp id

type instance AlgebraType0 AltArr f = ()
type instance AlgebraType  AltArr c = (Arrow c,ArrowChoice c,ArrowApply c)

instance FreeAlgebra2 AltArr where
  liftFree2 = \fab -> ACons fab NilQ
  foldNatFree2 = foldAltArr
  codom2  = Proof
--  forget2 :: forall (f :: k -> k -> Type). AlgebraType AltArr f => Proof (AlgebraType0 AltArr f) (AltArr f)
  forget2 = Proof

instance Semigroup (AltArr f o o) where
  f <> g = f . g

instance Monoid (AltArr f o o) where
    mempty = AId
    mappend = (<>)

instance Profunctor (AltArr f) where
  dimap fl fr a = arr fr . a . arr fl

instance ProfunctorFunctor AltArr where
  promap f = foldAltArr (liftFree2 . f)

instance ProfunctorMonad AltArr where
  proreturn = liftFree2
  projoin = joinAltArr

instance Strong (AltArr f) where
  first' = first
  second' = second

instance Choice (AltArr f) where
  left' = left
  right' = right

--instance Closed p => Closed (AltArr p) where
--  closed = hoistFree2 closed

arrowToMonad :: ArrowApply ar => ar a b -> a -> ArrowMonad ar b
arrowToMonad ar a = ArrowMonad (ar . arr (const a) )

unArrowMonad (ArrowMonad ar) = ar
runArrowMonad :: ArrowApply ar => ar (ArrowMonad ar b) b
runArrowMonad = app <<< arr unArrowMonad &&& arr (const ())

instance Traversing (AltArr f) where
  traverse' pab = proc fa -> do
    fb <- runArrowMonad -< mapM (arrowToMonad pab) fa
    returnA -< fb
