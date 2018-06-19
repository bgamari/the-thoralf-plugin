{-# LANGUAGE TypeFamilies, TypeInType, GADTs,
    DataKinds, AllowAmbiguousTypes,
    OverloadedLabels, StandaloneDeriving,
    TypeOperators, ScopedTypeVariables, TypeApplications
#-}

{-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


module Main where


import ThoralfPlugin.Theory.FiniteMap 
import ThoralfPlugin.Singletons.Symbol
import qualified ThoralfPlugin.Theory.DisEq as D

import Data.Kind ( Type )
import GHC.TypeLits ( Symbol )
import Data.Singletons.TypeLits
import System.IO (hFlush, stdin, stdout)


import GHC.TypeLits

data a :~: b where
  Refl :: a :~: a


-------------------------------------------------------
-- Nats
-------------------------------------------------------


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



-------------------------------------------------------
-- Finite Maps
-------------------------------------------------------

type LOne = '[ '(2,"hi"), '(1,"ok") ]
type LTwo = '[ '(1,"ok"), '(2,"hi") ]

-- Example 1
fmtest1 :: (FromList LOne) :~: (FromList LTwo)
fmtest1 = Refl


deleteTwice :: (DelField m1 m2 "bob", DelField m2 m3 "bob") => m2 :~: m3
deleteTwice = Refl

altTwice :: (AddField m1 m2 "ok" 2, AddField m2 m3 "ok" 2) => m2 :~: m3
altTwice = Refl

-- DONE
--symtest :: forall (a :: Symbol). "hi" :~: a
--symtest = Refl



----------------------  Row Types    ------------------------

data RowType :: (Fm Symbol Type) -> Type where
    EmptyRec :: RowType Nil
    AddField :: AddField m m' field val =>
                RowType m -> SSymbol field -> val ->
                RowType m'
    DelField :: DelField m m' field =>
                RowType m -> SSymbol field -> val ->
                RowType m'


getPrice :: Has m "price" Int => RowType m -> Int
getPrice (DelField rec fld val) = getPrice rec
getPrice (AddField rec fld val) =
  case (scomp fld (SSym @"price")) of
    D.Refl -> val
    D.DisRefl -> getPrice rec

pRecPrice :: PricedRec -> Int
pRecPrice (PRec rec) = getPrice rec


data PricedRec where
  PRec :: Has m "price" Int => 
          RowType m -> PricedRec


totalPrice :: [PricedRec] -> Int
totalPrice = sum . (map pRecPrice)

car = PRec
  (AddField (AddField EmptyRec (SSym @"price") (9000 :: Int)) 
  (SSym @"make") 
  ("honda" :: String))

plane = PRec
  (AddField (AddField EmptyRec (SSym @"pilot") ("zhang" :: String))
  (SSym @"price")
  (12000 :: Int))


main :: IO ()
main = do
  let sumTest = totalPrice [car, plane]
  putStrLn ("Total value: " ++ (show sumTest))


