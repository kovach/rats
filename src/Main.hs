module Main where

import Prelude hiding (Word, lex)
import Data.List
import Data.Maybe (fromMaybe)
import System.Environment (getArgs)

import Server (runServer)
import DrawDiagram.Main (runDrawDiagram)
import TestPipeline (runTestPipeline)
import CatShelf (runCatShelf)
import CatShelf
import ConcatParse
import Compile
import Basic (pp)

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
      let filename = case rest of
            (f:_) -> f
            []    -> error "usage: rats test-pipeline <base>"
          base = fromMaybe filename (stripSuffix ".turn" filename)
      runTestPipeline base
    ("ooops" : rest) -> do
      let filename = case rest of
            (f:_) -> f
            []    -> error "usage: rats ooops <base>"
          base = fromMaybe filename (stripSuffix ".turn" filename)
      runCatShelf base
    _ -> error "usage: rats <serve|draw-diagram|test-pipeline> ..."

stripSuffix :: String -> String -> Maybe String
stripSuffix suffix s
  | suffix `isSuffixOf` s = Just (Data.List.take (length s - length suffix) s)
  | otherwise = Nothing
