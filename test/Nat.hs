{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}

{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

{-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}

module Nat where

import ThoralfPlugin.Theory.Bool
import Data.Type.Equality
import Data.Kind
import GHC.TypeLits

test1 :: 1 :~: 1
test1 = Refl

test2 :: (a + 1) :~: (1 + a)
test2 = Refl

test3 :: (a + b) :~: (b + a)
test3 = Refl

{-
test3Bad :: (a + b) :~: b
test3Bad = Refl
-}

test4 :: (a + b) :~: (a + a) -> a :~: b
test4 Refl = Refl

data Vec :: Nat -> Type -> Type where
  VNil :: Vec 0 a
  (:>) :: a -> Vec n a -> Vec (1+n) a

deriving instance Show a => Show (Vec n a)
infixr 5 :>

concatVec :: Vec n a -> Vec m a -> Vec (n+m) a
concatVec VNil ys = ys
concatVec (x:> xs) ys = x :> (concatVec xs ys)

snocVec :: a -> Vec n a -> Vec (1+n) a
snocVec x VNil = x :> VNil
snocVec x (y :> ys) = y :> (snocVec x ys)


reverseVec :: Vec n a -> Vec n a
reverseVec VNil = VNil
reverseVec (x :> xs) = snocVec x (reverseVec xs)

{-
stripPrefix :: Eq a => Vec n a -> Vec m a -> Maybe (Vec (m - n) a)
stripPrefix VNil      ys        = Just ys
stripPrefix _         VNil       = Nothing
stripPrefix (x :> xs) (y :> ys) =
  if x == y
  then stripPrefix xs ys
  else Nothing
-}

ltTrans :: forall (a :: Nat) (b :: Nat) (c :: Nat).
  (a <? b) :~: True -> (b <? c) :~: True -> (a <? c) :~: True
ltTrans Refl Refl = Refl
