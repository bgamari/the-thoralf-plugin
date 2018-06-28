{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}


-- GHC plugin option
{-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}

-- Other options
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


module Main where


import ThoralfPlugin.Theory.FiniteMap
import ThoralfPlugin.Singletons.Symbol
import qualified ThoralfPlugin.Theory.DisEq as D

import Data.Type.Equality
import Data.Kind ( Type )
import GHC.TypeLits ( Symbol )
import Data.Singletons.TypeLits
import System.IO (hFlush, stdin, stdout)


import GHC.TypeLits


main :: IO ()
main = return ()


-- {-

-- | Simple Tests

test1 :: 1 :~: 1
test1 = Refl

test2 :: (a + 1) :~: (1 + a)
test2 = Refl

test3 :: (a + b) :~: (b + a)
test3 = Refl

test4 :: (a + (1 + b)) :~: ((a + b) + 1)
test4 = Refl

{-
test3Bad :: (a + b) :~: b
test3Bad = Refl
-}

test5 :: (a + b) :~: (a + a) -> a :~: b
test5 Refl = Refl


-- -}

-- | Length indexed vectors


data Vec :: Nat -> Type -> Type where
  VNil :: Vec 0 a
  (:>) :: a -> Vec n a -> Vec (n + 1) a

deriving instance Show a => Show (Vec n a)
infixr 5 :>

-- {-

concatVec :: Vec n a -> Vec m a -> Vec (n+m) a
concatVec VNil ys = ys
concatVec (x:> xs) ys = x :> (concatVec xs ys)

snocVec :: a -> Vec n a -> Vec (1+n) a
snocVec x VNil = x :> VNil
snocVec x (y :> ys) = y :> (snocVec x ys)


reverseVec :: Vec n a -> Vec n a
reverseVec VNil = VNil
reverseVec (x :> xs) = snocVec x (reverseVec xs)

-- -}

stripPrefix :: Eq a => Vec n a -> Vec m a -> Maybe (Vec (m - n) a)
stripPrefix VNil      ys        = Just ys
stripPrefix _         VNil       = Nothing
stripPrefix (x :> xs) (y :> ys) =
  if x == y
  then stripPrefix xs ys
  else Nothing

l1 = "hi" :> "bob" :> "jones" :> VNil
l2 = "hi" :> "bob" :> VNil




-- | Boolean Predicates on Nats ...

-- Easy. I just haven't implemented it. Would you like to?

{-

   Predicates can be encoded with boolean functions.

   For instance, (n < m) can be encoded as
     (LT n m) ~ True


-- Ascending order
data SortedNats :: Nat -> Type where
  NilSN :: SortedNats n
  ConsSN :: GT m n => SNat m -> SortedNats n -> SortedNats m


-}











