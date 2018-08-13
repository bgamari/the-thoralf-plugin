{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}

module ThoralfPlugin.Encode.UoM ( uomTheory ) where

import qualified SimpleSMT as SMT
import TyCon ( TyCon(..), tyConKind )
import Type ( Type, classifyPredType, PredTree(..),
              EqRel(..), splitTyConApp_maybe, isStrLitTy,
              splitFunTy_maybe, getTyVar_maybe, tyVarKind,
              tyConAppTyCon_maybe,
              mkStrLitTy, PredType, mkPrimEqPred,
              isTyVar, typeKind, nonDetCmpType, coreView,
              isNumLitTy
            )
import TcPluginM ( tcPluginIO, tcPluginTrace
                 , tcLookupTyCon, lookupOrig, tcLookupClass
                 , findImportedModule, FindResult(..), zonkCt
                 , unsafeTcPluginTcM, TcPluginM(..)
                 )
import OccName ( mkTcOcc )
import Module ( Module, mkModuleName )
import FastString ( unpackFS, fsLit )

import ThoralfPlugin.Encode.TheoryEncoding


uomTheory :: TcPluginM TheoryEncoding
uomTheory = do
  (Found location uomModule) <- findImportedModule fmModName (Just pkg)
  baseTyCon <- findTyCon uomModule "Base"
  oneTyCon <- findTyCon uomModule "One"
  divTyCon <- findTyCon uomModule "/:"
  mulTyCon <- findTyCon uomModule "*:"
  uomTyCon <- findTyCon uomModule "UoM"
  return $ mkFmBox baseTyCon oneTyCon divTyCon mulTyCon uomTyCon
  where
    fmModName = mkModuleName "ThoralfPlugin.Theory.UoM"
    pkg = fsLit "thoralf-plugin"



findTyCon :: Module -> String -> TcPluginM TyCon
findTyCon md strNm = do
    name <- lookupOrig md (mkTcOcc strNm)
    tcLookupTyCon name


mkFmBox :: TyCon -> TyCon -> TyCon -> TyCon -> TyCon -> TheoryEncoding
mkFmBox base one div mult uom =  emptyTheory 
  { startDecs = []
  , typeConvs =
    [ baseConvert base
    , oneConvert one
    , divConvert div
    , mulConvert mult
    ]
  , kindConvs = [uomConvert uom]
  }


baseConvert :: TyCon -> Type -> Maybe TyStrMaker
baseConvert base ty = do
  (tcon, (measure : power : xs)) <- splitTyConApp_maybe ty
  case tcon == base of
    False -> Nothing
    True ->
      let
        tyList =  measure :> power :> VNil
      in
        Just $ TyKit (tyList, VNil, baseString)


baseString :: Vec Two String -> Vec Zero String -> String
baseString (measure :> power :> VNil) VNil =
  let
    one = "((as const (Array String Int)) 0)"
  in "(store " ++ one ++ " " ++ measure ++ " " ++ power ++ ")"


oneConvert :: TyCon -> Type -> Maybe TyStrMaker
oneConvert one ty = do
  (tcon, _) <- splitTyConApp_maybe ty
  case tcon == one of
    False -> Nothing
    True ->
      let
        one = "((as const (Array String Int)) 0)"
      in
        Just $ TyKit (VNil, VNil, const . const $ one)



divConvert :: TyCon -> Type -> Maybe TyStrMaker
divConvert div ty = do
  (tcon, (n : m : xs)) <- splitTyConApp_maybe ty
  case tcon == div of
    False -> Nothing
    True ->
      let
        tyList = n :> m :> VNil
      in
        Just $ TyKit (tyList, VNil, divString)


type Two = 'Succ ('Succ 'Zero)
divString :: Vec Two String -> Vec Zero String -> String
divString (n :> m :> VNil) VNil =
    "((_ map (- (Int Int) Int)) " ++ n ++ " " ++ m ++ ")"



mulConvert :: TyCon -> Type -> Maybe TyStrMaker
mulConvert mult ty = do
  (tcon, (n : m : xs)) <- splitTyConApp_maybe ty
  case tcon == mult of
    False -> Nothing
    True ->
      let
        tyList = n :> m :> VNil
      in
        Just $ TyKit (tyList, VNil, mulString)


mulString :: Vec Two String -> Vec Zero String -> String
mulString (n :> m :> VNil) VNil =
    "((_ map (+ (Int Int) Int)) " ++ n ++ " " ++ m ++ ")"



uomConvert :: TyCon -> Type -> Maybe KdStrMaker
uomConvert uom ty = do
  (tcon, _) <- splitTyConApp_maybe ty
  case tcon == uom of
    False -> Nothing
    True -> Just $ KdKit (VNil, const "(Array String Int)")


