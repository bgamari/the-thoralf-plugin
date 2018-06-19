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

module ThoralfPlugin.Singletons.Symbol where

import Data.Singletons.TypeLits ( SSymbol(..), symbolVal, Sing(..) )
import Unsafe.Coerce

import ThoralfPlugin.Theory.DisEq
import Data.Proxy ( Proxy(..) )
import Data.Kind ( Constraint, Type )

scomp :: SSymbol s -> SSymbol s' -> s :~?~: s'
scomp (SSym :: Sing s) (SSym :: Sing s') =
  case (symbolVal (Proxy :: Proxy s)) == (symbolVal (Proxy :: Proxy s')) of
    True ->  unsafeCoerce  Refl
    False ->
      case (unsafeCoerce (Dict :: Dict ()) :: Dict (DisEquality s s')) of
        (Dict :: Dict (DisEquality s s')) -> DisRefl


data Dict :: Constraint -> Type where
  Dict :: a => Dict a



