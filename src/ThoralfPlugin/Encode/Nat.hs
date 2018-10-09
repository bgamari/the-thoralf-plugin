{-# LANGUAGE CPP, TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}
module ThoralfPlugin.Encode.Nat ( natTheory ) where

import GhcPlugins ( getUnique, TyCon )
import TysWiredIn ( typeNatKindCon )
import TcTypeNats ( typeNatAddTyCon, typeNatSubTyCon, typeNatMulTyCon, typeNatExpTyCon
#if MIN_VERSION_base(4,11,0)
                  , typeNatDivTyCon, typeNatModTyCon
#endif
                  )
import Type ( Type, TyVar, splitTyConApp_maybe, tyVarKind, isNumLitTy )
import TcRnTypes( TcPluginM )

import ThoralfPlugin.Encode.TheoryEncoding


natTheory :: TcPluginM TheoryEncoding
natTheory = return natEncoding

natEncoding :: TheoryEncoding
natEncoding = emptyTheory
  { typeConvs = [ natLitConv
                , binaryOpConv typeNatAddTyCon "+"
                , binaryOpConv typeNatSubTyCon "-"
                , binaryOpConv typeNatMulTyCon "*"
#if MIN_VERSION_base(4,11,0)
                , binaryOpConv typeNatDivTyCon "div"
                , binaryOpConv typeNatModTyCon "mod"
#endif
                ]
  , kindConvs = [natKindConv]
  , tyVarPreds = assertIntIsNat
  }


natLitConv :: Type -> Maybe TyConvCont
natLitConv ty = do
  integer <- isNumLitTy ty
  return $
    TyConvCont VNil VNil ((const . const) (show integer)) []

type Two = 'Succ ('Succ 'Zero)

binaryOpConv :: TyCon -> String
             -> Type -> Maybe TyConvCont
binaryOpConv tycon0 op ty = do
  (tycon, types) <- splitTyConApp_maybe ty
  case (tycon == tycon0, types) of
    (True, [x,y]) ->
      let
        mkNatSExpr :: Vec Two String -> Vec 'Zero String -> String
        mkNatSExpr (a :> b :> VNil) VNil = "(" ++ op ++ " " ++ a ++ " " ++ b ++ ")"
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






