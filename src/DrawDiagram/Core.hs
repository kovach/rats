module DrawDiagram.Core where

import Data.Maybe
import Data.List
import Diagrams.Prelude
import Diagrams.Backend.SVG

import DrawDiagram.Layout

-- | Pixels per unit of time.
unitWidth :: Double
unitWidth = 40

-- | Height of a single interval bar.
barHeight :: Double
barHeight = 30

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
      label = text (ivType iv) # fontSizeL 20 # fc black
      group = (label `atop` bar)
            # svgAttr "onmouseover" "this.classList.add('highlight')"
            # svgAttr "onmouseout" "this.classList.remove('highlight')"
      piece = (p2 (x, y), group)
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
    titled = (titleLabel ||| strutX 15 ||| dia) # frame 30

