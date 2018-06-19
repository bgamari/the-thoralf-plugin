{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving 
#-}

module ThoralfPlugin.Box.Symbol ( symbolSeed ) where

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
import TysWiredIn ( maybeTyCon, promotedNothingDataCon, promotedJustDataCon
                  , liftedTypeKind, typeSymbolKind, typeSymbolKindCon
                  )


import ThoralfPlugin.Box.TheoryBox


symbolSeed :: TheorySeed
symbolSeed = return symbolBox

symbolBox :: TheoryBox
symbolBox =
  emptyBox { typeConvs = [symLitConv]
           , kindConvs = [symKindConv]
           }

symLitConv :: Type -> Maybe TyStrMaker
symLitConv ty = do
  fastStr <- isStrLitTy ty
  let str = unpackFS fastStr
  let sexprStr = "\"" ++ str ++ "\""
  return $ TyKit (VNil, VNil, (const . const) sexprStr)


symKindConv :: Type -> Maybe KdStrMaker
symKindConv ty = do
  (tcon, _) <- splitTyConApp_maybe ty
  case tcon == typeSymbolKindCon of
    False -> Nothing
    True ->
      Just $ KdKit (VNil, const "String")
















