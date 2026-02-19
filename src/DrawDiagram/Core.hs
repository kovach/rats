module DrawDiagram.Core where

import Data.Maybe
import Data.List
import Diagrams.Prelude
import Diagrams.Backend.SVG
import qualified Data.Text as T
import qualified Graphics.Svg as Svg

import DrawDiagram.Layout

-- | Pixels per unit of time.
unitWidth :: Double
unitWidth = 40

-- | Height of a single interval bar.
barHeight :: Double
barHeight = 10

-- | Vertical gap between parent and child rows.
rowGap :: Double
rowGap = 5

-- | Render a list of top-level intervals into a diagram.
renderIntervals :: [Interval] -> Diagram B
renderIntervals ivs = position $ concat $ zipWith renderAt [0..] $ sortOn ivStart ivs

-- | Render an interval and its children, offset by a vertical depth.
renderAt :: Int -> Interval -> [(P2 Double, Diagram B)]
renderAt colorIndex iv =
  let w = fromIntegral (floor $ ivEnd iv - ivStart iv) * unitWidth
      x = fromIntegral (floor $ ivStart iv) * unitWidth + w / 2
      depth = floor $ fromJust $ ivNesting iv
      -- y = negate (fromIntegral depth * (barHeight + rowGap))
      y = negate (fromIntegral (depth) * (barHeight + rowGap))
      bar = roundedRect w barHeight 10 # fc (depthColour colorIndex) # lc black # lw thin
      label = text (ivType iv) # fontSizeL 6 # fc black
      labeledBar = ((label # translateX 0 # translateY (0)) `atop` (bar))
            # svgAttr "onmouseover" "this.classList.add('highlight')"
            # svgAttr "onmouseout" "this.classList.remove('highlight')"
      piece = (p2 (x, y), labeledBar)
  in [piece]

depthColour :: Int -> Colour Double
depthColour i = colors !! (i `mod` length colors)
  where
    colors = map (lighten 0.3) [steelblue, mediumseagreen, coral, plum]

lighten :: Double -> Colour Double -> Colour Double
lighten t c = blend t white c

makeDiagram (IntervalDiagram {title, content}) = (l, titled)
  where
    l = layout content
    dia = renderIntervals l # alignBL
    titleLabel = text title # fontSizeL 10 # fc black -- # alignL # alignT
    titled = (titleLabel ||| strutX (fromIntegral $ 3 * length title) ||| dia) # frame 30

writeDiagram fn iD = do
  let (_ivs, dia) = makeDiagram iD
      opts = SVGOptions absolute (Just cssDefs) (T.pack "") [] True
      svgElement = renderDia SVG opts dia
      path = "diagrams/" <> fn
  print (title iD, _ivs)
  Svg.renderToFile path svgElement

cssDefs :: Svg.Element
cssDefs = Svg.style_ [] $ Svg.toElement $ T.pack
  ".highlight { fill: yellow !important; fill-opacity: 0.85 !important; }"
