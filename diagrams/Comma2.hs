-- | Generates comma2.svg.
-- Run with: runghc Comma2.hs comma2.svg
module Main where

import Control.Monad.Writer (Writer, execWriter, tell)
import Numeric (showFFloat)
import System.Environment (getArgs)

-- ---------------------------------------------------------------------------
-- Types

data Color = Color Int Int Int

-- | Rectangle is specified by (left, right, top, bottom).
-- DottedLine and Label use (x1,y1,x2,y2) and (cx,cy,text) respectively.
data Shape
  = Rectangle Double Double Double Double  -- left right top bottom
  | DottedLine Double Double Double Double -- x1 y1 x2 y2
  | Label Double Double String             -- cx cy text

-- ---------------------------------------------------------------------------
-- Rendering helpers

showColor :: Color -> String
showColor (Color r g b) = "rgb(" ++ show r ++ "," ++ show g ++ "," ++ show b ++ ")"

-- | Format a Double for SVG coordinate output.
n :: Double -> String
n x = showFFloat (Just 4) x ""

highlightAttrs :: String
highlightAttrs =
  "onmouseout=\"this.classList.remove('highlight')\" " ++
  "onmouseover=\"this.classList.add('highlight')\""

shapeGroupAttrs :: Color -> String
shapeGroupAttrs color =
  "stroke-linejoin=\"miter\" fill-opacity=\"1.0\" fill=\"" ++ showColor color ++ "\" " ++
  "stroke=\"rgb(0,0,0)\" stroke-linecap=\"butt\" " ++ highlightAttrs ++ " " ++
  "stroke-miterlimit=\"10.0\" stroke-opacity=\"1.0\" stroke-width=\"0.5\""

labelGroupAttrs :: Color -> String
labelGroupAttrs color =
  "stroke-linejoin=\"miter\" fill-opacity=\"1.0\" font-size=\"6.0px\" " ++
  "fill=\"" ++ showColor color ++ "\" stroke=\"" ++ showColor color ++ "\" " ++
  "stroke-linecap=\"butt\" " ++ highlightAttrs ++ " " ++
  "stroke-miterlimit=\"10.0\" stroke-opacity=\"1.0\" stroke-width=\"0.5\""

-- ---------------------------------------------------------------------------
-- Shape generator

type Svg = Writer String

line :: String -> Svg ()
line s = tell (s ++ "\n")

gen :: Shape -> Color -> Svg ()

gen (Rectangle l r t b) color = do
  let w = r - l
      h = b - t
      rx = 5.0 :: Double
  line $ "<g " ++ shapeGroupAttrs color ++ ">"
  line $ "  <rect x=\"" ++ n l ++ "\" y=\"" ++ n t ++ "\" width=\"" ++ n w ++
         "\" height=\"" ++ n h ++ "\" rx=\"" ++ n rx ++ "\" ry=\"" ++ n rx ++ "\"/>"
  line "</g>"

gen (DottedLine x1 y1 x2 y2) color =
  line $
    "<line x1=\"" ++ n x1 ++ "\" y1=\"" ++ n y1 ++
    "\" x2=\"" ++ n x2 ++ "\" y2=\"" ++ n y2 ++
    "\" stroke=\"" ++ showColor color ++ "\" stroke-width=\"0.5\"" ++
    " stroke-dasharray=\"2,2\" fill=\"none\"/>"

gen (Label cx cy txt) color = do
  line $ "<g " ++ labelGroupAttrs color ++ ">"
  line $
    "  <text transform=\"matrix(1.0000,0.0000,0.0000,1.0000," ++ n cx ++ "," ++ n cy ++ ")\"" ++
    " stroke=\"none\" dominant-baseline=\"middle\" text-anchor=\"middle\">" ++ txt ++ "</text>"
  line "</g>"

-- ---------------------------------------------------------------------------
-- SVG wrapper

svgOpen :: Double -> Double -> String
svgOpen w h = unlines
  [ "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
  , "<!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1//EN\""
  , "    \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd\">"
  , "<svg font-size=\"1\" viewBox=\"0.0 0.0 " ++ n w ++ " " ++ n h ++ "\""
  , "     stroke=\"rgb(0,0,0)\" xmlns=\"http://www.w3.org/2000/svg\""
  , "     width=\"" ++ n w ++ "\" stroke-opacity=\"1\" height=\"" ++ n h ++ "\""
  , "     version=\"1.1\" xmlns:xlink=\"http://www.w3.org/1999/xlink\">"
  , "  <defs><style>.highlight { fill: yellow !important; fill-opacity: 0.85 !important; }</style></defs>"
  ]

svgClose :: String
svgClose = "</svg>"

-- ---------------------------------------------------------------------------
-- Diagram

diagram :: Svg ()
diagram = do
  tell (svgOpen 180 100)

  -- Vertical dotted guide lines: left edge of b (x=69), right edge of a (x=111)
  -- Starting beneath both a and b (y=57), down to bottom of c (y=82)
  gen (DottedLine 69 57 69 82) (Color 0 0 0)
  gen (DottedLine 111 57 111 82) (Color 0 0 0)

  -- ?b: green rectangle (lower right), center (110,50)
  gen (Rectangle 70 150 45 55) (Color 156 206 173)
  gen (Label 110 50 "? b") (Color 0 0 0)

  -- ?a: blue rectangle (upper left), center (70,35)
  gen (Rectangle 30 110 30 40) (Color 158 180 206)
  gen (Label 70 35 "? a") (Color 0 0 0)

  -- !c: amber rectangle (new, below), center (90,77)
  gen (Rectangle 70 110 72 82) (Color 236 180 58)
  gen (Label 90 77 "! c") (Color 0 0 0)

  line svgClose

main :: IO ()
main = do
  args <- getArgs
  case args of
    [outFile] -> writeFile outFile (execWriter diagram)
    _         -> ioError (userError "usage: Comma2 <output.svg>")
