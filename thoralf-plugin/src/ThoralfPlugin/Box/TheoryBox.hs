{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving 
#-}
module ThoralfPlugin.Box.TheoryBox
  ( SExpr, TheoryBox(..), TypeConv
  , TyStrMaker(..), KindConv, KdStrMaker(..)
  , Vec(..), TheorySeed, sumSeeds, Nat(..), emptyBox
  , sExprStr
  ) where

import Type ( Type, Kind )
import qualified Data.Kind as Kind
import qualified SimpleSMT as SMT


import TcRnTypes( TcPluginM )

type SExpr = SMT.SExpr


type TheorySeed = TcPluginM TheoryBox

data TheoryBox where
  TheoryBox ::
    { typeConvs :: [TypeConv]
    , kindConvs :: [KindConv]
    , startDecs :: [SExpr]
    } -> TheoryBox

type TypeConv = Type -> Maybe TyStrMaker
type KindConv = Type -> Maybe KdStrMaker

data TyStrMaker where
  TyKit ::
    ( Vec n Type
    , Vec m Kind
    , Vec n String -> Vec m String -> String) -> TyStrMaker

data KdStrMaker where
  KdKit :: (Vec m Kind, Vec m String -> String) -> KdStrMaker

sExprStr :: SExpr -> String
sExprStr exp = SMT.showsSExpr exp ""


-- Length indexed vectors are needed for Ty & Kd StrMaker's
data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

data Vec :: Nat -> Kind.Type -> Kind.Type where
  VNil :: Vec Zero a
  (:>) :: a -> Vec n a -> Vec (Succ n) a
infixr 5 :>


sumSeeds :: [TheorySeed] -> TheorySeed
sumSeeds [] = return emptyBox
sumSeeds (x:xs) = do
  boxHead <- x
  boxTail <- sumSeeds xs
  return $ addBoxes boxHead boxTail

emptyBox = TheoryBox { typeConvs = []
                     , kindConvs = []
                     , startDecs = []
                     }

addBoxes :: TheoryBox -> TheoryBox -> TheoryBox
addBoxes box1 box2 =
  let
    tyConvs = typeConvs box1 ++ typeConvs box2
    kdConv = kindConvs box1 ++ kindConvs box2
    decs = startDecs box1 ++ startDecs box2
  in
    TheoryBox
    { typeConvs = tyConvs
    , kindConvs = kdConv
    , startDecs = decs
    }




-----------------------------------------------------------------------------
-- Library Features
-----------------------------------------------------------------------------











