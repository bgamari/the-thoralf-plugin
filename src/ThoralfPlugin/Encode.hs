{-# LANGUAGE CPP #-}

module ThoralfPlugin.Encode ( thoralfTheories ) where


#if MIN_VERSION_ghc(9, 2, 0)
import GHC.Tc.Plugin ( TcPluginM )
#else
import TcRnTypes( TcPluginM )
#endif

import ThoralfPlugin.Encode.TheoryEncoding

import ThoralfPlugin.Encode.Nat ( natTheory )
import ThoralfPlugin.Encode.FiniteMap ( fmTheory )
import ThoralfPlugin.Encode.UoM ( uomTheory )
import ThoralfPlugin.Encode.Symbol ( symbolTheory )
import ThoralfPlugin.Encode.Bool ( boolTheory )


thoralfTheories :: TcPluginM TheoryEncoding
thoralfTheories = sumEncodings
  [ natTheory
  , fmTheory
  , symbolTheory
  , boolTheory
  , uomTheory
  ]









