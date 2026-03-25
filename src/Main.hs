module Main where

import Data.List (isSuffixOf)
import qualified Data.List
import Data.Maybe (fromMaybe)
import System.Environment (getArgs)

import Server (runServer)
import DrawDiagram.Main (runDrawDiagram)
import TestPipeline (runTestPipeline)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("serve" : rest) -> do
      let filename = case rest of
            (f:_) -> f
            []    -> error "usage: rats serve <file.turn>"
          base = fromMaybe filename (stripSuffix ".turn" filename)
      runServer base
    ("draw-diagram" : _) -> runDrawDiagram
    ("test-pipeline" : rest) -> do
      let base = case rest of
            (f:_) -> f
            []    -> error "usage: rats test-pipeline <base>"
      runTestPipeline base
    _ -> error "usage: rats <serve|draw-diagram|test-pipeline> ..."

stripSuffix :: String -> String -> Maybe String
stripSuffix suffix s
  | suffix `isSuffixOf` s = Just (Data.List.take (length s - length suffix) s)
  | otherwise = Nothing
