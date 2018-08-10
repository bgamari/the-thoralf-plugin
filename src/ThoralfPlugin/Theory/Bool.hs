{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wunused-top-binds #-}

module ThoralfPlugin.Theory.Bool
( type (<?) )
where

import Data.Kind ( Type, Constraint )

type family (<?) (x :: a) (y :: a) :: Bool where {}


