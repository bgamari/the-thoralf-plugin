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
  , SCompare (..)
  , compareSym
  )
where

import ThoralfPlugin.Theory.DisEq
import ThoralfPlugin.Theory.Bool

import Data.Kind ( Constraint, Type )
import GHC.TypeLits ( symbolVal, Symbol, KnownSymbol (..) )
import Unsafe.Coerce


data SSymbol :: Symbol -> Type where
  SSym :: KnownSymbol s => SSymbol s

scomp :: SSymbol s -> SSymbol s' -> s :~?~: s'
scomp s@(SSym :: SSymbol s) s'@(SSym :: SSymbol s') =
  case symbolVal s == symbolVal s' of
    True ->  unsafeCoerce  Refl
    False -> forceCT @(DisEquality s s') DisRefl


data SCompare s s' where
  SEQ :: s ~ s'         => SCompare s s'
  SLT :: s <? s' ~ True => SCompare s s'
  SGT :: s' <? s ~ True => SCompare s s'

compareSym :: forall s s'. SSymbol s -> SSymbol s' -> SCompare s s'
compareSym s@(SSym) s'@(SSym) =
  case compare (symbolVal s) (symbolVal s') of
    EQ -> forceCT @(s ~ s') SEQ
    LT -> forceCT @(s <? s' ~ True) SLT
    GT -> forceCT @(s' <? s ~ True) SGT





-- Forcing Constraints

forceCT :: forall c x. (c => x) -> x
forceCT x = case unsafeCoerce (Dict :: Dict ()) :: Dict c of
  (Dict :: Dict c) -> x

data Dict :: Constraint -> Type where
  Dict :: a => Dict a



