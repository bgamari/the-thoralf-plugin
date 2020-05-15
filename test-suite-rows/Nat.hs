{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}

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

NOTE: Expected failure for test3Bad.

• Couldn't match type ‘b’ with ‘a + b’
  ‘b’ is a rigid type variable bound by
    the type signature for:
      test3Bad :: forall (a :: Nat) (b :: Nat). (a + b) :~: b
  Expected type: (a + b) :~: b
    Actual type: b :~: b
• In the expression: Refl
  In an equation for ‘test3Bad’: test3Bad = Refl
• Relevant bindings include
    test3Bad :: (a + b) :~: b
-}

test4 :: (a + b) :~: (a + a) -> a :~: b
test4 Refl = Refl

ltTrans
  :: forall (a :: Nat) (b :: Nat) (c :: Nat)
  . (a <? b) :~: 'True
  -> (b <? c) :~: 'True
  -> (a <? c) :~: 'True
ltTrans Refl Refl = Refl

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

stripPrefix :: Eq a => Vec n a -> Vec m a -> Maybe (Vec (m - n) a)
stripPrefix VNil ys = Just ys
stripPrefix _ VNil = Nothing
stripPrefix (x :> xs) (y :> ys) = if x == y then stripPrefix xs ys else Nothing

vecTests :: IO ()
vecTests = do
  let v = 1 :> 2 :> (VNil :: Vec 0 Int)
  let w = 3 :> 4 :> (VNil :: Vec 0 Int)
  let vw = concatVec v w
  putStrLn ("[1,2] = " ++ (show v))
  putStrLn ("reverse [1,2] = " ++ (show $ reverseVec v))
  putStrLn ("concat [1,2] [3,4] = " ++ (show vw))
  putStrLn ("snoc 3 [1,2] = " ++ (show $ snocVec 3 v))
  putStrLn ("stripPrefix [1,2] [1,2,3,4] = " ++ (show $ stripPrefix v vw))
  putStrLn ("stripPrefix [3,4] [1,2,3,4] = " ++ (show $ stripPrefix w vw))
  putStrLn ("stripPrefix [] [1,2,3,4] = " ++ (show $ stripPrefix VNil vw))
  putStrLn ("stripPrefix [1,2] [] = " ++ (show $ stripPrefix v VNil))
