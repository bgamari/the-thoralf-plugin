{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}

{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

{-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}

module FiniteMaps where

import ThoralfPlugin.Theory.FiniteMap
import Data.Type.Equality

-- import GHC.TypeLits -- Uncomment for symtest

type LOne = '[ '(2,"hi"), '(1,"ok") ]
type LTwo = '[ '(1,"ok"), '(2,"hi") ]

-- Example 1
fmtest1 :: (FromList LOne) :~: (FromList LTwo)
fmtest1 = Refl

deleteTwice :: (DelField m1 m2 "bob", DelField m2 m3 "bob") => m2 :~: m3
deleteTwice = Refl

altTwice :: (AddField m1 m2 "ok" 2, AddField m2 m3 "ok" 2) => m2 :~: m3
altTwice = Refl

{-
symtest :: forall (a :: Symbol). "hi" :~: a
symtest = Refl

NOTE: Expected failure for symtest.

• Couldn't match type ‘a’ with ‘"hi"’
  ‘a’ is a rigid type variable bound by
    the type signature for:
      symtest :: forall (a :: Symbol). "hi" :~: a
  Expected type: "hi" :~: a
    Actual type: "hi" :~: "hi"
• In the expression: Refl
  In an equation for ‘symtest’: symtest = Refl
• Relevant bindings include
    symtest :: "hi" :~: a
-}

-- Union Test
union1 ::
  ( UnionFm a b ab
  , UnionFm ab c abc
  , UnionFm b c bc
  , UnionFm a bc abc'
  ) => abc :~: abc'
union1 = Refl

-- Intersect Test
intersect1 ::
  ( IntersectFm a b ab
  , IntersectFm ab c abc
  , IntersectFm b c bc
  , IntersectFm a bc abc'
  ) => abc :~: abc'
intersect1 = Refl
