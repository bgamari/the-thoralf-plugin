{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Variables where


#if MIN_VERSION_ghc(9, 2, 0)
import GHC.Core.Type ( TyVar )
import GHC.Core.Coercion ( Var )
import GHC.Types.Var ( isTcTyVar )
import GHC.Tc.Utils.TcType ( isMetaTyVar )
#else
import Var ( TyVar, Var, isTcTyVar )
import TcType ( isMetaTyVar )
#endif

data VarCat = Tau | Skol | Irr
  deriving Eq

categorizeVar :: Var -> VarCat
categorizeVar var =
  if isTcTyVar var
  then
    if isMetaTyVar var
    then Tau
    else Skol
  else Irr

isSkolemVar :: Var -> Bool
isSkolemVar v = categorizeVar v == Skol

isTauVar :: TyVar -> Bool
isTauVar v = categorizeVar v == Tau

