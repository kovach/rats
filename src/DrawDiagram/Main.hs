{-# LANGUAGE OverloadedStrings #-}
module DrawDiagram.Main where

import Diagrams.Prelude
import Diagrams.Backend.SVG
import DrawDiagram.Core
import DrawDiagram.Layout

runDrawDiagram :: IO ()
runDrawDiagram = do
  sequence_ $ map writeDiagram demoDiagrams
  putStrLn $ "Wrote " ++ show (length demoDiagrams) ++ " SVGs and diagram.html"
