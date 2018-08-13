{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Encode.TheoryEncoding
  ( TheoryEncoding (..)
  , emptyTheory
  , TyConvCont (..)
  , KdConvCont (..)
  , DecCont (..)
  , sumEncodings

  , Vec(..)
  , Nat(..)
  ) where



import Type ( Type, Kind )
import TcRnTypes( TcPluginM )
import Data.Vec



-- $theoryEncoding
data TheoryEncoding where
  TheoryEncoding ::
    { kindConvs :: [Type -> Maybe KdConvCont]
    , typeConvs :: [Type -> Maybe TyConvCont]
    , startDecs :: [String]      -- Top level, never changing declarations
    } -> TheoryEncoding

-- $theoryEncoding
--
-- To encode a theory into SMT, we essentially need to provide functions
-- that can take a GHC type (that is not a type variable) and turn it
-- into a SMT expression. To blend theories, this is done with
-- continuations. Each conversion function only converts part of a type,
-- and provides a pair of subterms and a function to use the converted subterms.
--
-- Encoding a theory also requires converting GHC variables to SMT
-- variables. This needs conversion functions that convert the GHC Kind of
-- a variable into a valid SMT sort, again using
-- continuations. Lastly, some type conversions require SMT functions over
-- generic SMT data types. Since SMT doesn't support polymorhphic
-- functions, these functions need to be unique per the kind of their
-- arguments. These are continuations in 'DecCont'.


-- | A Kind Conversion Continuation
data KdConvCont where
  KdConvCont ::
    { kdConvKinds :: Vec m Kind
    , kdConvCont :: Vec m String -> String
    } -> KdConvCont


-- | A Type Conversion Continuation
data TyConvCont where
  TyConvCont ::
    { tyConvTypes :: Vec n Type
    , tyConvKinds :: Vec m Kind
    , tyConvCont :: Vec n String -> Vec m String -> String
    , tyConvDecs :: [DecCont]
    } -> TyConvCont

-- $decCont
data DecCont where
  DecCont ::
    { decContKds :: Vec n Kind
    , decCont :: Vec n String -> Hash -> [String]
    } -> DecCont

type Hash = String

-- $decCont
--
-- These are declaration continuations. These are data types for building
-- local SMT declarations. SMT declarations are simply a list of strings
-- that are valid SMT commands, after which some function symbol becomes
-- meaningful and can be used when converting a type. These declarations
-- are local because the definition of these function symbols depend on the
-- sorts of their inputs. These sorts are determined by converting the
-- kinds into a list of strings and feeding that to the 'decCont' function.
--
-- A 'DecCont' must satisfy the property that two declarations are the same
-- if and only if the converted list of kinds are the same. Then, to make
-- each declaration different, we must provide a hash of the converted list
-- of kinds that can be used in a SMT identifier. A converted kind will not
-- suffice. For example, for a function symbol for the length of a linked
-- list of arrays from @Int@ to @Bool@, the identifier @len(Array Int
-- Bool)@ is not a valid name, whereas, @len1@ is a valid name.
--

-- TODO: Clarify the above.




-- * Helpful functions
--------------------------------------------------------------------------------


-- | Combining monadic theory encodings
sumEncodings :: [TcPluginM TheoryEncoding] -> TcPluginM TheoryEncoding
sumEncodings = fmap (foldl addEncodings emptyTheory) . sequence


-- | An empty theory from which you can build any theory.
emptyTheory :: TheoryEncoding
emptyTheory = TheoryEncoding
  { typeConvs = []
  , kindConvs = []
  , startDecs = []
  }

addEncodings :: TheoryEncoding -> TheoryEncoding -> TheoryEncoding
addEncodings encode1 encode2 = TheoryEncoding
  { typeConvs = typeConvs encode1 ++ typeConvs encode2
  , kindConvs = kindConvs encode1 ++ kindConvs encode2
  , startDecs = startDecs encode1 ++ startDecs encode2
  }



