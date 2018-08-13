{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}
module ThoralfPlugin.Encode.Nat ( natTheory ) where

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
import TcRnTypes( TcPluginM )

import ThoralfPlugin.Encode.TheoryEncoding


natTheory :: TcPluginM TheoryEncoding
natTheory = return natEncoding

natEncoding :: TheoryEncoding
natEncoding = emptyTheory
  { typeConvs = [natLitConv, natAddConv, natSubConv]
  , kindConvs = [natKindConv]
  }


natLitConv :: Type -> Maybe TyConvCont
natLitConv ty = do
  integer <- isNumLitTy ty
  return $
    TyConvCont VNil VNil ((const . const) (show integer)) []

type Two = 'Succ ('Succ 'Zero)

natAddConv :: Type -> Maybe TyConvCont
natAddConv ty = do
  (tycon, types) <- splitTyConApp_maybe ty
  case (tycon == typeNatAddTyCon, types) of
    (True, [x,y]) ->
      let
        mkNatSExpr :: Vec Two String -> Vec Zero String -> String
        mkNatSExpr (a :> b :> VNil) VNil = "(+ " ++ a ++ " " ++ b ++ ")"
        tyList = x :> y :> VNil
      in
        return $ TyConvCont tyList VNil mkNatSExpr []
    (_, _) -> Nothing



natSubConv :: Type -> Maybe TyConvCont
natSubConv ty = do
  (tycon, types) <- splitTyConApp_maybe ty
  case (tycon == typeNatSubTyCon, types) of
    (True, [x,y]) ->
      let
        mkNatSExpr :: Vec Two String -> Vec Zero String -> String
        mkNatSExpr (a :> b :> VNil)  VNil = "(- " ++ a ++ " " ++ b ++ ")"
        tyList = x :> y :> VNil
      in
        return $ TyConvCont tyList VNil mkNatSExpr []
    (_, _) -> Nothing


natKindConv :: Type -> Maybe KdConvCont
natKindConv ty = do
  (tycon, _) <- splitTyConApp_maybe ty
  case tycon == typeNatKindCon of
    True -> return $ KdConvCont VNil (const "Int")
    False -> Nothing






