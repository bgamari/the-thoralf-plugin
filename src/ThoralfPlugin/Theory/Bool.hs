{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wunused-top-binds #-}

module ThoralfPlugin.Theory.Bool where

import GHC.TypeLits ( Nat )

type family (<?) (x :: Nat) (y :: Nat) :: Bool where {}
type family (<=?) (x :: Nat) (y :: Nat) :: Bool where {}



