{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Encode.TheoryEncoding
  ( SExpr
  , sExprStr

  , TheoryEncoding(..)
  , emptyTheory
  , TypeConv
  , TyStrMaker(..)
  , KindConv
  , KdStrMaker(..)
  , sumEncodings

  , Vec(..)
  , Nat(..)
  ) where



import Type ( Type, Kind )
import qualified SimpleSMT as SMT
import TcRnTypes( TcPluginM )

import Data.Vec

type SExpr = SMT.SExpr


data TheoryEncoding where
  TheoryEncoding ::
    { typeConvs :: [TypeConv]
    , kindConvs :: [KindConv]
    , startDecs :: [SExpr]
    } -> TheoryEncoding

type TypeConv = Type -> Maybe TyStrMaker
type KindConv = Type -> Maybe KdStrMaker

data TyStrMaker where
  TyKit ::
    ( Vec n Type
    , Vec m Kind
    , Vec n String -> Vec m String -> String) -> TyStrMaker

data KdStrMaker where
  KdKit :: (Vec m Kind, Vec m String -> String) -> KdStrMaker




-- * Helpful functions
--------------------------------------------------------------------------------

-- | Printing the string of an SExpr
sExprStr :: SExpr -> String
sExprStr sexp = SMT.showsSExpr sexp ""


-- | Combining monadic theory encodings
sumEncodings :: [TcPluginM TheoryEncoding] -> TcPluginM TheoryEncoding
sumEncodings = fmap (foldl addEncodings emptyTheory) . sequence


-- | An empty theory from which you can build any theory.
emptyTheory :: TheoryEncoding
emptyTheory = TheoryEncoding { typeConvs = []
                     , kindConvs = []
                     , startDecs = []
                     }

addEncodings :: TheoryEncoding -> TheoryEncoding -> TheoryEncoding
addEncodings box1 box2 =
  let
    tyConvs = typeConvs box1 ++ typeConvs box2
    kdConv = kindConvs box1 ++ kindConvs box2
    decs = startDecs box1 ++ startDecs box2
  in
    TheoryEncoding
    { typeConvs = tyConvs
    , kindConvs = kdConv
    , startDecs = decs
    }


