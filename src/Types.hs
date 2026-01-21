module Types where

import Data.Char

class PP a where
  pp  :: a -> String

capitalize = map toUpper
