{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.Vec where

import Data.Kind


data Vec :: Nat -> Type -> Type where
  VNil :: Vec Zero a
  (:>) :: a -> Vec n a -> Vec (Succ n) a
infixr 5 :>


data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat



vecMapAll :: (a -> Maybe b) -> Vec n a -> Maybe (Vec n b)
vecMapAll f VNil = Just VNil
vecMapAll f (x :> xs) = do
  b <- f x
  bs <- vecMapAll f xs
  return (b :> bs)

vecMapList :: (a -> b) -> Vec n a -> [b]
vecMapList f VNil = []
vecMapList f (x :> xs) = (f x) : (vecMapList f xs)

vecMap :: (a -> b) -> Vec n a -> Vec n b
vecMap f VNil = VNil
vecMap f (x :> xs) = (f x) :> (vecMap f xs)


