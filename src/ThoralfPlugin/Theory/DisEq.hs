{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ThoralfPlugin.Theory.DisEq ( DisEquality, (:~?~:)(..) ) where

--import Data.Kind ( Constraint )


class DisEquality (x :: k) (y :: k) where {}


data a :~?~: b where
  Refl :: a :~?~: a
  DisRefl :: DisEquality a b => a :~?~: b





