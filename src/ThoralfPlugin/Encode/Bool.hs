{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}

module ThoralfPlugin.Encode.Bool ( boolTheory ) where

import TysWiredIn ( boolTyCon, promotedTrueDataCon, promotedFalseDataCon )

import TyCon ( TyCon(..), tyConKind )

import TcPluginM ( tcPluginIO, tcPluginTrace
                 , tcLookupTyCon, lookupOrig, tcLookupClass
                 , findImportedModule, FindResult(..), zonkCt
                 , unsafeTcPluginTcM, TcPluginM(..)
                 )

import Type ( Type, classifyPredType, PredTree(..),
              EqRel(..), splitTyConApp_maybe, isStrLitTy,
              splitFunTy_maybe, getTyVar_maybe, tyVarKind,
              tyConAppTyCon_maybe,
              mkStrLitTy, PredType, mkPrimEqPred,
              isTyVar, typeKind, nonDetCmpType, coreView,
              isNumLitTy
            )

import qualified Data.Kind as Kind

import OccName ( mkTcOcc )
import Module ( Module, mkModuleName )
import FastString ( unpackFS, fsLit )



import ThoralfPlugin.Encode.TheoryEncoding


boolTheory :: TcPluginM TheoryEncoding
boolTheory = do
  let boolModM = findImportedModule boolMod $ Just pkg
  Found location boolModule <- boolModM
  compTyCon <- findTyCon boolModule "<?"
  return $ boolEncoding compTyCon
  where
    boolMod = mkModuleName "ThoralfPlugin.Theory.Bool"
    pkg = fsLit "thoralf-plugin"

    findTyCon :: Module -> String -> TcPluginM TyCon
    findTyCon md strNm = do
        name <- lookupOrig md (mkTcOcc strNm)
        tcLookupTyCon name



boolEncoding :: TyCon -> TheoryEncoding
boolEncoding compTyCon = emptyTheory
  { typeConvs = [trueLitConv, falseLitConv, compLitConv compTyCon]
  , kindConvs = [boolKindConv]
  }




-- * The Conversion Functions
-------------------------------------------------------------------------------


trueLitConv :: Type -> Maybe TyConvCont
trueLitConv ty = do
  (tcon,xs) <- splitTyConApp_maybe ty
  case tcon == promotedTrueDataCon of
    True -> return $
      TyConvCont VNil VNil (const . const $ "true") []
    False -> Nothing



falseLitConv :: Type -> Maybe TyConvCont
falseLitConv ty = do
  (tcon,xs) <- splitTyConApp_maybe ty
  case tcon == promotedFalseDataCon of
    True -> return $
      TyConvCont VNil VNil (const . const $ "false") []
    False -> Nothing


compLitConv :: TyCon -> Type -> Maybe TyConvCont
compLitConv comp ty = do
  (tycon, types) <- splitTyConApp_maybe ty
  case (tycon == comp, types) of
    (True, (x : y : xs)) -> return $
        TyConvCont (x :> y :> VNil) VNil compMaker []
    _ -> Nothing


type Two = 'Succ ('Succ 'Zero)
compMaker :: Vec Two String -> Vec Zero String -> String
compMaker (x :> y :> VNil) VNil = "(< " ++ x ++ " " ++ y ++ ")"


boolKindConv :: Type -> Maybe KdConvCont
boolKindConv ty = do
  (tycon, xs) <- splitTyConApp_maybe ty
  case tycon == boolTyCon of
    True -> return $ KdConvCont VNil (const "Bool")
    False -> Nothing







