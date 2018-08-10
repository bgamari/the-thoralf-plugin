{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}
module ThoralfPlugin.Box.Nat ( natSeed ) where

import TysWiredIn ( typeNatKindCon )
import TcTypeNats ( typeNatAddTyCon, typeNatSubTyCon )
import qualified SimpleSMT as SMT
import Type ( Type, classifyPredType, PredTree(..),
              EqRel(..), splitTyConApp_maybe, isStrLitTy,
              splitFunTy_maybe, getTyVar_maybe, tyVarKind,
              tyConAppTyCon_maybe,
              mkStrLitTy, PredType, mkPrimEqPred,
              isTyVar, typeKind, nonDetCmpType, coreView,
              isNumLitTy
            )
import qualified Data.Kind as Kind

import ThoralfPlugin.Box.TheoryBox


natSeed :: TheorySeed
natSeed = return natBox

natBox = emptyBox
  { typeConvs = [natLitConv, natAddConv, natSubConv]
  , kindConvs = [natKindConv]
  }


natLitConv :: Type -> Maybe TyStrMaker
natLitConv ty = do
  integer <- isNumLitTy ty
  return $ TyKit (VNil, VNil, (const . const) (show integer))


natAddConv :: Type -> Maybe TyStrMaker
natAddConv ty = do
  (tycon, types) <- splitTyConApp_maybe ty
  case (tycon == typeNatAddTyCon, types) of
    (True, [x,y]) ->
      let
        mkNatSExpr :: Vec (Succ (Succ Zero)) String -> Vec Zero String ->  String
        mkNatSExpr (a :> b :> VNil)  VNil = "(+ " ++ a ++ " " ++ b ++ ")"
        tyList = x :> y :> VNil
      in
        return $ TyKit (tyList, VNil, mkNatSExpr)
    (_, _) -> Nothing



natSubConv :: Type -> Maybe TyStrMaker
natSubConv ty = do
  (tycon, types) <- splitTyConApp_maybe ty
  case (tycon == typeNatSubTyCon, types) of
    (True, [x,y]) ->
      let
        mkNatSExpr :: Vec (Succ (Succ Zero)) String -> Vec Zero String -> String
        mkNatSExpr (a :> b :> VNil)  VNil = "(- " ++ a ++ " " ++ b ++ ")"
        tyList = x :> y :> VNil
      in
        return $ TyKit (tyList, VNil, mkNatSExpr)
    (_, _) -> Nothing


natKindConv :: Type -> Maybe KdStrMaker
natKindConv ty = do
  (tycon, _) <- splitTyConApp_maybe ty
  case tycon == typeNatKindCon of
    True -> return $ KdKit (VNil, const "Int")
    False -> Nothing







