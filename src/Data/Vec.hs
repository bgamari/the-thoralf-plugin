{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.Vec where

import Data.Kind
import Data.Monoid
import Prelude

data Vec :: Nat -> Type -> Type where
  VNil :: Vec 'Zero a
  (:>) :: a -> Vec n a -> Vec ('Succ n) a
infixr 5 :>


data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat


instance Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (x :> xs) = f x :> fmap f xs

instance Foldable (Vec n) where
  foldMap _ VNil = mempty
  foldMap f (x :> xs) = f x <> foldMap f xs


-- TODO: Replace vecMapAll and similar stuff with standard instances of
-- basic type classes.



vecMapAll :: Monad m =>
  (a -> m b) -> Vec n a -> m (Vec n b)
vecMapAll _ VNil = return VNil
vecMapAll f (x :> xs) = do
  b <- f x
  bs <- vecMapAll f xs
  return (b :> bs)

vecMapList :: (a -> b) -> Vec n a -> [b]
vecMapList _ VNil = []
vecMapList f (x :> xs) = (f x) : (vecMapList f xs)

vecMap :: (a -> b) -> Vec n a -> Vec n b
vecMap _ VNil = VNil
vecMap f (x :> xs) = (f x) :> (vecMap f xs)


