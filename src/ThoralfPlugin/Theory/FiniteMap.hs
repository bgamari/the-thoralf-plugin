{-# OPTIONS_GHC -Wunused-top-binds #-}
{-# LANGUAGE TypeFamilies, TypeInType,
 TypeOperators, GADTs, UndecidableInstances,
 RankNTypes, KindSignatures, ConstraintKinds
 #-}
module ThoralfPlugin.Theory.FiniteMap
  ( Fm, Nil
  , Has
  , Omits
  , FromList
  , AddField
  , DelField
  , UnionFm
  , IntersectFm
  ) where

import Data.Kind ( Type )


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
type family Nil :: Fm (k :: Type) (v :: Type) where {}

type family Alter (m :: Fm k v) (key :: k) (val :: v) :: Fm k v where {}

type family Delete (m :: Fm (k :: Type) (v :: Type)) (key :: k) :: Fm k v where {}

type family UnionL (m :: Fm (k :: Type) (v :: Type)) (m' :: Fm k v)
  :: Fm k v where {}

type family IntersectL (m :: Fm (k :: Type) (v :: Type)) (m' :: Fm k v)
  :: Fm k v where {}


------------------------------------------------------------------------


-- Contraints

type Has m k v = Alter m k v ~ m
type Omits m k = Delete m k ~ m
type AddField m m' k v = (Alter m k v) ~ m'
type DelField m m' k = (Delete m k) ~ m'
type UnionFm m1 m2 u = u ~ UnionL m1 m2
type IntersectFm m1 m2 i = i ~ IntersectL m1 m2

type family FromList (xs :: [(k,v)]) :: Fm k v where
  FromList '[] = Nil
  FromList ( '(k,v) : ys ) = (Alter (FromList ys) k v)




