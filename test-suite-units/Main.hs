module Main where

import Text.Printf (printf)
import UoM (Unit(..), calcDistance)

main :: IO ()
main =
  putStrLn $ printf "3 m/s for 2 s = %s m" (show $ calcDistance (MkUnit 3) (MkUnit 2))
