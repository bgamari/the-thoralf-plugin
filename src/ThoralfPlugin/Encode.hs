module ThoralfPlugin.Encode ( thoralfTheories ) where


import TcRnTypes( TcPluginM )

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









