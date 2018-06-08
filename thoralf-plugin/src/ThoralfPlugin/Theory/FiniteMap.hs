{-# OPTIONS_GHC -Wunused-top-binds #-}
{-# LANGUAGE TypeFamilies, TypeInType,
 TypeOperators, GADTs, UndecidableInstances,
 RankNTypes, KindSignatures
 #-}
module ThoralfPlugin.Theory.FiniteMap (
        Fm, Nil,
        Has, Omits, ConcreteFm,
        AddField, DelField
  ) where

import GHC.Types ( Symbol )
import Data.Kind ( Type, Constraint )
--import Type.Family.List ( (:<) )

type (:<) = '(:)
infixr 5 :<

{-

In this module the finite maps interface is declared.

-}


----------------------------------------------------------------------------
----------------------------------------------------------------------------
                          -- DATA DEFINITIONS --
----------------------------------------------------------------------------
----------------------------------------------------------------------------



data Fm :: forall k v. k -> v -> Type where {}

{- OLD
data TMaybe a
type family TNothing :: TMaybe (a :: Type) where {}
type family TJust (a :: k) :: TMaybe k where {}
-- TJust as a TyCon takes in two type args, a and k.
-- in the order k then a
-}


----------------------------------------------------------------------------
----------------------------------------------------------------------------
                          -- THE EXPOSED GRAMMAR --
----------------------------------------------------------------------------
----------------------------------------------------------------------------

-- The Encoding
type family Nil :: forall (k :: Type) (v :: Type). Fm k v where {}

type family Alter (m :: Fm k v) (key :: k) (val :: v)
  :: forall (k :: Type) (v :: Type). Fm k v where {}

type family Delete (m :: Fm k (v :: Type)) (key :: k)
  :: forall (k :: Type) (v :: Type). Fm k v where {}
------------------------------------------------------------------------


-- Interface
type family Has (f :: Fm k v) (key :: k) (val :: v) :: Constraint where
  Has m k v = (Alter m k v ~ m)

type family Omits (f :: Fm (k :: Type) (v :: Type)) (key :: k) :: Constraint where
  Omits m k = (Delete m k ~ m)

type family ConcreteFm (xs :: [(k,v)]) :: Fm k v where
  ConcreteFm xs = Build Nil xs

type family
  AddField (m :: Fm k v) (m' :: Fm k v) (key :: k) (val :: v)
  :: Constraint where
    AddField m m' k v = (Alter m k v) ~ m'

type family
  DelField (m :: Fm k (v :: Type)) (m' :: Fm k v) (key :: k)
  :: Constraint where
    DelField m m' k = (Delete m k) ~ m'
------------------------------------------------------------------------


type family Build (m :: Fm k v) (xs :: [(k, v)]) :: Fm k v where
  Build m '[] = m
  Build m ('(k,v) :< ys) = Build (Alter m k v) ys




