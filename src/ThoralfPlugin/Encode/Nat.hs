{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}
module ThoralfPlugin.Encode.Nat ( natTheory ) where

import GhcPlugins ( getUnique )
import TysWiredIn ( typeNatKindCon )
import TcTypeNats ( typeNatAddTyCon, typeNatSubTyCon )
import Type ( Type, TyVar, splitTyConApp_maybe, tyVarKind, isNumLitTy )
import TcRnTypes( TcPluginM )

import ThoralfPlugin.Encode.TheoryEncoding


natTheory :: TcPluginM TheoryEncoding
natTheory = return natEncoding

natEncoding :: TheoryEncoding
natEncoding = emptyTheory
  { typeConvs = [natLitConv, natAddConv, natSubConv]
  , kindConvs = [natKindConv]
  , tyVarPreds = assertIntIsNat
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
        mkNatSExpr :: Vec Two String -> Vec 'Zero String -> String
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
        mkNatSExpr :: Vec Two String -> Vec 'Zero String -> String
        mkNatSExpr (a :> b :> VNil)  VNil = "(- " ++ a ++ " " ++ b ++ ")"
        tyList = x :> y :> VNil
      in
        return $ TyConvCont tyList VNil mkNatSExpr []
    (_, _) -> Nothing


assertIntIsNat :: TyVar -> Maybe [String]
assertIntIsNat tv = do
  (KdConvCont _ _) <- natKindConv (tyVarKind tv)
  let name = show $ getUnique tv
  let isNat = "(assert (<= 0 " ++ name ++ "))"
  return [isNat]


natKindConv :: Type -> Maybe KdConvCont
natKindConv ty = do
  (tycon, _) <- splitTyConApp_maybe ty
  case tycon == typeNatKindCon of
    True -> return $ KdConvCont VNil (const "Int")
    False -> Nothing






