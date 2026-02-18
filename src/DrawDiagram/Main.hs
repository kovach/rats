{-# LANGUAGE OverloadedStrings #-}
module Main where

import Diagrams.Prelude
import Diagrams.Backend.SVG
import qualified Graphics.Svg as Svg
import qualified Data.Text as T
import DrawDiagram.Core
import DrawDiagram.Layout

main :: IO ()
main = do
  sequence_ $ zipWith writeDiagram ["diagram-" ++ show i ++ ".svg" | i <- [0..]] demoDiagrams
  writeFile "diagram.html" htmlPage
  putStrLn $ "Wrote " ++ show (length demoDiagrams) ++ " SVGs and diagram.html"

writeDiagram path iD = do
  let (ivs, dia) = makeDiagram iD
      opts = SVGOptions (mkWidth 800) (Just cssDefs) (T.pack "") [] True
      svgElement = renderDia SVG opts dia
  print (title iD, ivs)
  Svg.renderToFile path svgElement

cssDefs :: Svg.Element
cssDefs = Svg.style_ [] $ Svg.toElement $ T.pack
  ".highlight { fill: yellow !important; fill-opacity: 0.85 !important; }"

htmlPage :: String
htmlPage = unlines
  [ "<!DOCTYPE html>"
  , "<html><head><meta charset=\"utf-8\"><title>Diagram</title></head>"
  , "<body>"
  , "<div id=\"diagram\"></div>"
  , "<script>"
  , "fetch('diagram.svg')"
  , "  .then(r => r.text())"
  , "  .then(svg => { document.getElementById('diagram').innerHTML = svg; });"
  , "</script>"
  , "</body></html>"
  ]

diagram :: Diagram B
diagram = renderIntervals sampleIntervals # frame 10

sampleIntervals :: [Interval]
sampleIntervals =
  [ Interval 0 10 Nothing "process"
  , Interval 0 4  Nothing "init"
  , Interval 5 7  Nothing "work"
  , Interval 8 13 Nothing "cleanup"
  , Interval 14 18 Nothing "request"
  , Interval 14 15 Nothing "parse"
  , Interval 16 22 Nothing "respond!"
  ]
