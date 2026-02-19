{-# LANGUAGE OverloadedStrings #-}
module Main where

import Diagrams.Prelude
import Diagrams.Backend.SVG
import DrawDiagram.Core
import DrawDiagram.Layout

main :: IO ()
main = do
  sequence_ $ zipWith writeDiagram ["diagram-" ++ show i ++ ".svg" | i <- [0..]] demoDiagrams
  putStrLn $ "Wrote " ++ show (length demoDiagrams) ++ " SVGs and diagram.html"
