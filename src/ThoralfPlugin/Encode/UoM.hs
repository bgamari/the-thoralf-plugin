{-# LANGUAGE CPP,
    TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}

module ThoralfPlugin.Encode.UoM ( uomTheory ) where

#if MIN_VERSION_ghc(9, 2, 0)
import GHC.Plugins ( TyCon, mkTcOcc )
import GHC.Core.Type ( Type, splitTyConApp_maybe )
import GHC.Tc.Plugin
                 ( tcLookupTyCon, lookupOrig
                 , findImportedModule, FindResult(..)
                 , TcPluginM
                 )
import GHC.Unit.Module ( Module, mkModuleName )
import GHC.Data.FastString ( fsLit )
#else
import TyCon ( TyCon(..) )
import Type ( Type, splitTyConApp_maybe )
import TcPluginM ( tcLookupTyCon, lookupOrig
                 , findImportedModule, FindResult(..)
                 , TcPluginM
                 )
import OccName ( mkTcOcc )
import Module ( Module, mkModuleName )
import FastString ( fsLit )
#endif

import ThoralfPlugin.Encode.TheoryEncoding


uomTheory :: TcPluginM TheoryEncoding
uomTheory = do
  (Found _ uomModule) <- findImportedModule fmModName (Just pkg)
  baseTyCon <- findTyCon uomModule "Base"
  oneTyCon <- findTyCon uomModule "One"
  divTyCon <- findTyCon uomModule "/:"
  mulTyCon <- findTyCon uomModule "*:"
  uomTyCon <- findTyCon uomModule "UoM"
  return $ mkUoMEncoding baseTyCon oneTyCon divTyCon mulTyCon uomTyCon
  where
    fmModName = mkModuleName "ThoralfPlugin.Theory.UoM"
    pkg = fsLit "thoralf-plugin"



findTyCon :: Module -> String -> TcPluginM TyCon
findTyCon md strNm = do
    name <- lookupOrig md (mkTcOcc strNm)
    tcLookupTyCon name


mkUoMEncoding :: TyCon -> TyCon -> TyCon -> TyCon -> TyCon -> TheoryEncoding
mkUoMEncoding base one div' mult uom =  emptyTheory
  { typeConvs =
    [ baseConvert base
    , oneConvert one
    , divConvert div'
    , mulConvert mult
    ]
  , kindConvs = [uomConvert uom]
  }


baseConvert :: TyCon -> Type -> Maybe TyConvCont
baseConvert base ty = do
  (tcon, (measure : power : _)) <- splitTyConApp_maybe ty
  case tcon == base of
    False -> Nothing
    True -> let tyList =  measure :> power :> VNil in
      Just $ TyConvCont tyList VNil baseString []


baseString :: Vec Two String -> Vec 'Zero String -> String
baseString (measure :> power :> VNil) VNil =
  let one = "((as const (Array String Int)) 0)" in
  "(store " ++ one ++ " " ++ measure ++ " " ++ power ++ ")"


oneConvert :: TyCon -> Type -> Maybe TyConvCont
oneConvert one ty = do
  (tcon, _) <- splitTyConApp_maybe ty
  case tcon == one of
    False -> Nothing
    True ->
      let one' = "((as const (Array String Int)) 0)" in
      Just $ TyConvCont VNil VNil (const . const $ one') []



divConvert :: TyCon -> Type -> Maybe TyConvCont
divConvert divTycon ty = do
  (tcon, (n : m : _)) <- splitTyConApp_maybe ty
  case tcon == divTycon of
    False -> Nothing
    True ->
      let tyList = n :> m :> VNil in
      Just $ TyConvCont tyList VNil divString []


type Two = 'Succ ('Succ 'Zero)
divString :: Vec Two String -> Vec 'Zero String -> String
divString (n :> m :> VNil) VNil =
    "((_ map (- (Int Int) Int)) " ++ n ++ " " ++ m ++ ")"



mulConvert :: TyCon -> Type -> Maybe TyConvCont
mulConvert mult ty = do
  (tcon, (n : m : _)) <- splitTyConApp_maybe ty
  case tcon == mult of
    False -> Nothing
    True ->
      let tyList = n :> m :> VNil in
      Just $ TyConvCont tyList VNil mulString []


mulString :: Vec Two String -> Vec 'Zero String -> String
mulString (n :> m :> VNil) VNil =
    "((_ map (+ (Int Int) Int)) " ++ n ++ " " ++ m ++ ")"



uomConvert :: TyCon -> Type -> Maybe KdConvCont
uomConvert uom ty = do
  (tcon, _) <- splitTyConApp_maybe ty
  case tcon == uom of
    False -> Nothing
    True -> Just $ KdConvCont VNil (const "(Array String Int)")


