{-# OPTIONS_GHC -Wunused-top-binds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module ThoralfPlugin.Singletons.Symbol
  ( SSymbol (..)
  , scomp
  )
where

import ThoralfPlugin.Theory.DisEq

import Data.Kind ( Constraint, Type )
import GHC.TypeLits ( symbolVal, Symbol, KnownSymbol )
import Unsafe.Coerce


data SSymbol :: Symbol -> Type where
  SSym :: KnownSymbol s => SSymbol s

scomp :: SSymbol s -> SSymbol s' -> s :~?~: s'
scomp s@(SSym :: SSymbol s) s'@(SSym :: SSymbol s') =
  case symbolVal s == symbolVal s' of
    True ->  unsafeCoerce  Refl
    False -> forceCT @(DisEquality s s') DisRefl





-- Forcing Constraints

forceCT :: forall c x. (c => x) -> x
forceCT x = case unsafeCoerce (Dict :: Dict ()) :: Dict c of
  (Dict :: Dict c) -> x

data Dict :: Constraint -> Type where
  Dict :: a => Dict a



