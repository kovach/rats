{-# LANGUAGE OverloadedStrings #-}
module Main where

import Diagrams.Prelude
import Diagrams.Backend.SVG
import DrawDiagram.Core
import DrawDiagram.Layout

main :: IO ()
main = do
  sequence_ $ map writeDiagram demoDiagrams
  putStrLn $ "Wrote " ++ show (length demoDiagrams) ++ " SVGs and diagram.html"
