{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}

module ThoralfPlugin.Encode.FiniteMap ( fmTheory ) where

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


fmTheory :: TcPluginM TheoryEncoding
fmTheory = do
  (Found location fmModule) <- findImportedModule fmModName (Just pkg)
  nilTyCon <- findTyCon fmModule "Nil"
  alterTyCon <- findTyCon fmModule "Alter"
  deleteTyCon <- findTyCon fmModule "Delete"
  fmTyCon <- findTyCon fmModule "Fm"
  return $ mkFmBox nilTyCon alterTyCon deleteTyCon fmTyCon
  where
    fmModName = mkModuleName "ThoralfPlugin.Theory.FiniteMap"
    pkg = fsLit "thoralf-plugin"



findTyCon :: Module -> String -> TcPluginM TyCon
findTyCon md strNm = do
    name <- lookupOrig md (mkTcOcc strNm)
    tcLookupTyCon name


mkFmBox :: TyCon -> TyCon -> TyCon -> TyCon -> TheoryEncoding
mkFmBox nil alter delete fm =
  emptyTheory { startDecs = [maybeDef]
           , typeConvs =
             [ nilConvert nil
             , alterConvert alter
             , deleteConvert delete
             ]
           , kindConvs = [fmConvert fm]
           }

-- Data and constant declarations
maybeDef :: SExpr
maybeDef = SMT.Atom "(declare-datatypes (T) \
           \((Maybe nothing (just (fromJust T)))))"



{-
Reference:


TODO: eventually make this less of a hack.

-}
-- DO NOT MESS WITH THE ORDER

nilConvert :: TyCon -> Type -> Maybe TyStrMaker
nilConvert nil ty = do
  (tcon, (keyKind : valKind : xs)) <- splitTyConApp_maybe ty
  case tcon == nil of
    False -> Nothing
    True ->
      let
        kindList =  keyKind :> valKind :> VNil
      in
        Just $ TyKit (VNil, kindList, nilString)


nilString :: Vec Zero String -> Vec Two String -> String
nilString VNil (keyKindStr :> valKindStr :> VNil) =
  let
    maybeVal = " (Maybe " ++ valKindStr ++ ")"
    arrayTp = "(Array " ++ keyKindStr ++ " " ++ maybeVal ++ ")"
    nilStr = "((as const " ++ arrayTp ++ ") nothing)"
  in nilStr


alterConvert :: TyCon -> Type -> Maybe TyStrMaker
alterConvert alter ty = do
  (tcon, (_ : _ : fmTp : keyTp : valTp : xs)) <- splitTyConApp_maybe ty
  case tcon == alter of
    False -> Nothing
    True ->
      let
        tyList = fmTp :> keyTp :> valTp :> VNil
      in
        Just $ TyKit (tyList, VNil, alterString)


type Three = 'Succ ('Succ ('Succ 'Zero))
alterString :: Vec Three String -> Vec Zero String -> String
alterString (fmStr :> keyStr :> valStr :> VNil) VNil =
  let
    valueStr = "(just " ++ valStr  ++ ")"
    altStr =
      "(store " ++ fmStr ++ " " ++ keyStr ++ " " ++ valueStr ++ ")"
  in
    altStr


deleteConvert :: TyCon -> Type -> Maybe TyStrMaker
deleteConvert delete ty = do
  (tcon, (_ : _ : fmTp : keyTp : xs)) <- splitTyConApp_maybe ty
  case tcon == delete of
    False -> Nothing
    True ->
      let
        tyList = fmTp :> keyTp :> VNil
      in
        Just $ TyKit (tyList, VNil, deleteString)

type Two = 'Succ ('Succ 'Zero)
deleteString :: Vec Two String -> Vec Zero String -> String
deleteString (fmStr :> keyStr :> VNil) VNil =
  "(store " ++ fmStr ++ " " ++ keyStr ++ " nothing)"


fmConvert :: TyCon -> Type -> Maybe KdStrMaker
fmConvert fm ty = do
  (tcon, (_ : _ : keyKind : valKind : xs)) <- splitTyConApp_maybe ty
  case tcon == fm of
    False -> Nothing
    True ->
      let
        kindList = keyKind :> valKind :> VNil
      in
        Just $ KdKit (kindList, fmString)

fmString :: Vec Two String -> String
fmString (keyKindStr :> valKindStr :> VNil) =
  mkArrayTp keyKindStr valKindStr

mkArrayTp :: String -> String -> String
mkArrayTp keySort valSort =
  "(Array " ++ keySort ++ " (Maybe " ++ valSort ++ "))"



-------------------------------------
-- Lib Fns
-------------------------------------





