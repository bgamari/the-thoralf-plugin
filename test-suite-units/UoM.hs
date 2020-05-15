{-# LANGUAGE TypeFamilies, GADTs, DataKinds #-}

{-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}

module UoM where

import Data.Kind (Type)
import Data.Singletons.TypeLits hiding (SSymbol)
import ThoralfPlugin.Singletons.Symbol (SSymbol)
import ThoralfPlugin.Theory.UoM

-- | Interface
-------------------------------------------------------------

data Unit :: UoM -> Type where
  MkUnit :: Double -> Unit m

instance Show (Unit a) where
    show (MkUnit x) = show x

-- Note: we only expose this part of the interface:

scalar :: Double -> Unit One
scalar d = MkUnit d

mkUnit :: IsBase s n b => Double -> SSymbol s -> SNat n -> Unit b
mkUnit d _ _ = MkUnit d

add :: Unit a -> Unit a -> Unit a
add (MkUnit x) (MkUnit y) = MkUnit (x + y)

negate :: Unit a -> Unit a
negate (MkUnit x) = MkUnit (-x)

mult :: IsProd a b c => Unit a -> Unit b -> Unit c
mult (MkUnit x) (MkUnit y) = MkUnit (x * y)

div :: IsDiv a b c => Unit a -> Unit b -> Unit c
div (MkUnit x) (MkUnit y) = MkUnit (x / y)

extract :: Unit a -> Double
extract (MkUnit d) = d
-------------------------------------------------------------



-- | Use Case
-------------------------------------------------------------

-- velocity: m/s
-- time: s
-- distance = velocity * time
type Meters  = FromList '[ '("meters", 1) ]
type Seconds = FromList '[ '("secs",   1) ]

calcDistance
    :: IsDiv Meters Seconds metPerSec
    => Unit metPerSec
    -> Unit Seconds
    -> Unit Meters
calcDistance a b = mult a b

-------------------------------------------------------------
