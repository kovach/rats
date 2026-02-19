module Main where

import System.Environment (getArgs)
import Server (compileAndRun)

main :: IO ()
main = do
  args <- getArgs
  let base = case args of
        (f:_) -> f
        []    -> error "usage: test-pipeline <base>  (e.g. test-pipeline ttt)"
  compileAndRun base
