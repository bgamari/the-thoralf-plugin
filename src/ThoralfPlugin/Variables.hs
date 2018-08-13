{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Variables where


import Var ( TyVar, Var, isTcTyVar, varName )
import TcType ( eqType, isMetaTyVar, Kind, TcType, TcTyVar )

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

