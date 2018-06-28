{-# OPTIONS_GHC -Wunused-top-binds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}


module ThoralfPlugin.Theory.Bool (
  LT, LTE, GT, GTE
  ) where


import GHC.Types ( Symbol )
import Data.Kind ( Type, Constraint )
import GHC.TypeLits


-- | DATA DEFINITIONS

data Boolean where {}

type family ThoralfTrue :: Boolean where {}
type family ThoralfFalse :: Boolean where {}

------------------------------------------------------------------------


-- | Nat Predicates

-- Internal
type family ThorLT (n :: Nat) (m :: Nat) :: Boolean where {}
type family ThorLTE (n :: Nat) (m :: Nat) :: Boolean where {}
type family ThorGT (n :: Nat) (m :: Nat) :: Boolean where {}
type family ThorGTE (n :: Nat) (m :: Nat) :: Boolean where {}


-- Exposed
type family LT (n :: Nat) (m :: Nat) :: Constraint where
  LT n m = (ThorLT n m ~ ThoralfTrue)

type family LTE (n :: Nat) (m :: Nat) :: Constraint where
  LTE n m = (ThorLTE n m ~ ThoralfTrue)

type family GT (n :: Nat) (m :: Nat) :: Constraint where
  GT n m = (ThorGT n m ~ ThoralfTrue)

type family GTE (n :: Nat) (m :: Nat) :: Constraint where
  GTE n m = (ThorGTE n m ~ ThoralfTrue)



