module Main where

import Nat (vecTests)
import qualified FiniteMaps ()
import RowTypes (rowTests)

main :: IO ()
main = do
  vecTests
  rowTests
