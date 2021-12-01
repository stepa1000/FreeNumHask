{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Control.Free.Algebra.Cse where

import qualified Prelude
import Prelude (($),undefined)
--import Data.Function

import Control.Free.Algebra.Prelude

import Control.Free.Algebra.Arrow
--import Data.Functor.Foldable liftFree2
import Data.Foldable
import Control.Applicative

type FixLetVar b f = Fix (Let (Var b f) )

proLetFoldFix :: (Functor f, Traversable f)
              => p b a -> AltArr p (f a) a -> AltArr p (FixLetVar b f) a
proLetFoldFix pba pfaa = proLetFoldFix' $ proRunVar pba pfaa

proLetFoldFix' :: (Functor f, Traversable f )
              => AltArr p (Var b f a) a
              -> AltArr p (FixLetVar b f) a
proLetFoldFix' apba = proc flv -> do
  a <- runArrowMonad -< letFoldFixM (arrowToMonad apba) flv
  returnA -< a

data Var b f a =
    Exp (f a)
  | Var b

instance Functor f => Functor (Var b f) where
  fmap f (Exp fa) = Exp (fmap f fa)
  fmap f (Var b) = Var b

instance (Foldable f,Functor f) => Foldable (Var b f) where
  foldMap f (Exp fa) = (foldMap f fa)
  foldMap f (Var b) = mempty

instance Traversable f => Traversable (Var b f) where
  traverse f (Exp fa) = Exp <$> traverse f fa
  traverse _ (Var b) = pure $ Var b

annihilationVar :: Var b f a -> Either (f a) b
annihilationVar (Exp fa) = Left fa
annihilationVar (Var b) = Right b

--newtype FixVar f b = FixVar {unFixVar :: Fix (Var b f)}

runVar' :: (b -> a) -> (f a -> a) -> Var b f a -> a
runVar' f g (Var b) = f b
runVar' f g (Exp fa) = g fa

proRunVar :: Functor f => p b a -> AltArr p (f a) a -> AltArr p (Var b f a) a
proRunVar pba pfaa = proc fcbf -> do
  a <- id ||| id <<< pfaa +++ liftFree2 pba -< annihilationVar fcbf
  returnA -< a
{-}
runVar :: Functor f => (b -> a) -> (f a -> a) -> FixVar f b -> a
runVar f g (FixVar (Fix (Var b))) = f b
runVar f g (FixVar (Fix (Exp fa))) = g $ fmap (runVar f g . FixVar) fa
{-}
proRunVar :: Traversable f => p b a -> p (f a) a -> AltArr p (FixVar f b) a
proRunVar pba pfaa = proc fb -> do
  a <- wander <<< traverse' pba -< fb
-}
--  returnA -< a
--  where
--    c = proRunVar' pba pfaa . promap c . arr project

instance Functor f => Functor (FixVar f) where
  fmap f (FixVar (Fix (Exp fa))) = FixVar $ Fix $ Exp $ fmap (unFixVar . fmap f . FixVar) fa
  fmap f (FixVar (Fix (Var b) )) = FixVar $ Fix (Var (f b) )

instance (Foldable f,Functor f) => Foldable (FixVar f) where
  foldMap f (FixVar (Fix (Exp fa))) = fold (fmap (foldMap f . FixVar) fa)
  foldMap f (FixVar (Fix (Var b) )) = f b

instance Traversable f => Traversable (FixVar f) where -- . fmap (Fix . Var) unFixVar
  traverse f (FixVar (Fix (Exp fa))) = (FixVar . Fix . Exp ) <$>
    traverse (fmap unFixVar .traverse f . FixVar) fa
-}
