{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving
#-}

module ThoralfPlugin.Encode.FiniteMap ( fmTheory ) where

import TyCon ( TyCon(..) )
import Type ( Type, splitTyConApp_maybe )
import TcPluginM ( tcLookupTyCon, lookupOrig
                 , findImportedModule, FindResult(..)
                 , TcPluginM
                 )
import OccName ( mkTcOcc )
import Module ( Module, mkModuleName )
import FastString ( fsLit )
import Data.Hashable ( hash )

import ThoralfPlugin.Encode.TheoryEncoding


fmTheory :: TcPluginM TheoryEncoding
fmTheory = do
  (Found location fmModule) <- findImportedModule fmModName (Just pkg)
  nil <- findTyCon fmModule "Nil"
  alt <- findTyCon fmModule "Alter"
  del <- findTyCon fmModule "Delete"
  union <- findTyCon fmModule "UnionL"
  inter <- findTyCon fmModule "IntersectL"
  fm <- findTyCon fmModule "Fm"
  return $ mkFmTheory (nil, alt, del, union, inter, fm)
  where
    fmModName = mkModuleName "ThoralfPlugin.Theory.FiniteMap"
    pkg = fsLit "thoralf-plugin"



findTyCon :: Module -> String -> TcPluginM TyCon
findTyCon md strNm = do
    name <- lookupOrig md (mkTcOcc strNm)
    tcLookupTyCon name


type FmTyCons = (TyCon, TyCon, TyCon, TyCon, TyCon, TyCon)

mkFmTheory :: FmTyCons-> TheoryEncoding
mkFmTheory (nil, alter, delete, union, inter, fm) =
  emptyTheory { startDecs = [maybeDef]
           , typeConvs =
             [ nilConvert nil
             , alterConvert alter
             , deleteConvert delete
             , unionConvert union
             , interConvert inter
             ]
           , kindConvs = [fmConvert fm]
           }

-- Data and constant declarations
maybeDef :: String
maybeDef =
  "(declare-datatypes (T) ((Maybe nothing (just (fromJust T)))))"



{-
Reference:


TODO: eventually make this less of a hack.

-}

type One = 'Succ 'Zero
type Two = 'Succ One
type Three = 'Succ Two

nilConvert :: TyCon -> Type -> Maybe TyConvCont
nilConvert nil ty = do
  (tcon, (keyKind : valKind : xs)) <- splitTyConApp_maybe ty
  True <- return $ tcon == nil
  let kindList =  keyKind :> valKind :> VNil
  return $ TyConvCont VNil kindList nilString []
  where

  nilString :: Vec 'Zero String -> Vec Two String -> String
  nilString VNil (keyKindStr :> valKindStr :> VNil) = nilStr where
    maybeVal = " (Maybe " ++ valKindStr ++ ")"
    arrayTp = "(Array " ++ keyKindStr ++ " " ++ maybeVal ++ ")"
    nilStr = "((as const " ++ arrayTp ++ ") nothing)"


alterConvert :: TyCon -> Type -> Maybe TyConvCont
alterConvert alter ty = do
  (tcon, (_ : _ : fmTp : keyTp : valTp : xs)) <- splitTyConApp_maybe ty
  True <- return $ tcon == alter
  let tyList = fmTp :> keyTp :> valTp :> VNil
  return $ TyConvCont tyList VNil alterString []
  where

  alterString :: Vec Three String -> Vec 'Zero String -> String
  alterString (fmStr :> keyStr :> valStr :> VNil) VNil = altStr where
    valueStr = "(just " ++ valStr  ++ ")"
    altStr = "(store " ++ fmStr ++ " " ++ keyStr ++ " " ++ valueStr ++ ")"


deleteConvert :: TyCon -> Type -> Maybe TyConvCont
deleteConvert delete ty = do
  (tcon, (_ : valKd : fmTp : keyTp : xs)) <- splitTyConApp_maybe ty
  True <- return $ tcon == delete
  let tyList = fmTp :> keyTp :> VNil
  let kdList = valKd :> VNil
  return $ TyConvCont tyList kdList deleteString []
  where

  deleteString :: Vec Two String -> Vec One String -> String
  deleteString (fmStr :> keyStr :> VNil) (valKd :> VNil) =
    "(store " ++ fmStr ++ " " ++ keyStr ++ 
    " (as nothing (Maybe " ++ valKd ++ ") )  )"



unionConvert :: TyCon -> Type -> Maybe TyConvCont
unionConvert union ty = do
  (tcon, tys) <- splitTyConApp_maybe ty
  let match = (tcon == union, tys)
  (True, _:valKd:m1:m2:_)  <- return match
  let tys = m1 :> m2 :> VNil
  let kds = valKd :> VNil
  let decCont = DecCont kds "either" eitherDec
  return $ TyConvCont tys kds unionStr [decCont]
  where


  unionStr :: Vec Two String -> Vec One String -> String
  unionStr (m1 :> m2 :> VNil) (valKd :> VNil) =
    "( (_ map " ++ eith ++ " ) " ++ m1 ++ " " ++ m2 ++ " )"
    where

    eith = "either" ++ hashVal
    hashVal = show $ hash valKd

  eitherDec :: Vec One String -> [String]
  eitherDec (valKd :> VNil) = let hashVal = show $ hash valKd in
    [ "(declare-fun either" ++ hashVal ++ " ((Maybe "++ valKd ++ ") \
      \(Maybe "++ valKd ++ ")) (Maybe " ++ valKd ++"))"
    , "(assert (forall ((y (Maybe " ++ valKd ++ "))) \
      \(= (either" ++ hashVal ++ " (as nothing (Maybe " ++
        valKd ++ ") ) y) y)))"
    , "(assert (forall ((x (Maybe " ++ valKd ++ ")) (y (Maybe " ++ valKd ++
      "))) (=> ((_ is (just (" ++ valKd ++ ") (Maybe " ++ valKd ++
      ") ) ) x) (= (either" ++ hashVal ++ " x y) x))))"
    ]


interConvert :: TyCon -> Type -> Maybe TyConvCont
interConvert intersect ty = do
  (tcon, tys) <- splitTyConApp_maybe ty
  let match = (tcon == intersect, tys)
  (True, _:valKd:m1:m2:_)  <- return match
  let tys = m1 :> m2 :> VNil
  let kds = valKd :> VNil
  let decCont = DecCont kds "both" bothDec
  return $ TyConvCont tys kds interStr [decCont]
  where

  interStr :: Vec Two String -> Vec One String -> String
  interStr (m1 :> m2 :> VNil) (valKd :> VNil) = 
    "( (_ map " ++ both ++") "++ m1 ++ " " ++ m2 ++")"
    where

    both = "both" ++ hashVal
    hashVal = show $ hash valKd

  bothDec :: Vec One String -> [String]
  bothDec (valKd :> VNil) =
    [ "(declare-fun both" ++ hashVal ++ 
      " ((Maybe " ++ valKd ++ ") (Maybe " ++
        valKd ++ ")) (Maybe " ++ valKd ++ "))"
    , "(assert (forall ((y (Maybe " ++ valKd ++ "))) \
      \(= (both" ++ hashVal ++ " y " ++ noth ++ ") " ++ noth ++ ")))"
    , "(assert (forall ((y (Maybe " ++ valKd ++
      "))) (= (both" ++ hashVal ++ " nothing y) nothing)))"
    , "(assert (forall ((x (Maybe " ++ valKd ++ ")) (y (Maybe " ++ 
      valKd ++ "))) (=> (and ((_ is " ++ jus ++ 
      ") x) ((_ is "++ jus ++") y) ) (= (both" ++ hashVal ++ " x y) x))))"
    ] where

        hashVal = show $ hash valKd 
        noth = "(as nothing (Maybe " ++ valKd ++ "))"
        jus = "(just ("++ valKd ++ ") (Maybe "++ valKd ++ "))"



fmConvert :: TyCon -> Type -> Maybe KdConvCont
fmConvert fm ty = do
  (tcon, (_ : _ : keyKind : valKind : xs)) <- splitTyConApp_maybe ty
  True <- return $ tcon == fm
  let kindList = keyKind :> valKind :> VNil
  return $ KdConvCont kindList fmString
  where

  fmString :: Vec Two String -> String
  fmString (keyKindStr :> valKindStr :> VNil) =
    mkArrayTp keyKindStr valKindStr

  mkArrayTp :: String -> String -> String
  mkArrayTp keySort valSort =
    "(Array " ++ keySort ++ " (Maybe " ++ valSort ++ "))"




