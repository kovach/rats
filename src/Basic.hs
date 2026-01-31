module Basic where

import Data.Char
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

class PP a where
  pp  :: a -> String

instance (PP a, PP b) => PP (a, b) where
  pp (a,b) = "(" <> pp a <> ", " <> pp b <> ")"

instance PP a => PP [a] where
  pp xs = "[" <> intercalate ", " (map pp xs) <> "]"

instance PP a => PP (Set a) where
  pp xs = "{" <> intercalate ", " (Set.toList $ Set.map pp xs) <> "}"

instance (PP k, PP a) => PP (Map k a) where
  pp xs = "{{" <> intercalate ", " (map pp . Map.toList $ xs) <> "}}"

instance PP Char where
  pp c = [c]

--instance (PP a, Traversable f) => PP (f a) where
--  pp xs = "[" <> intercalate ", " (map pp $ traverse (\a -> [a]) xs) <> "]"

pprint :: PP a => a -> IO ()
pprint = putStrLn . pp

-- PP string utils
pwrap x = "(" <> x <> ")"
capitalize = map toUpper
bwrap x = "[" <> x <> "]"
spwrap x = " " <> x <> " "
commas = intercalate ", "
args = pwrap . intercalate ", "

assert a b | a == b = putStrLn "ok"
assert a b = error $ "not-equal:\n" <> pp a <> "\n\n" <> pp b

class Monoid b => Collection a b | b -> a where
  none :: b
  one :: a -> b
  ofList :: [a] -> b
  ofList = mconcat . map one
  none = mempty
  size :: b -> Int
  member :: a -> b -> Bool
instance Ord a => Collection a (Set a) where
  one = Set.singleton
  size = length
  member = elem
instance Eq a => Collection a [a] where
  one x = [x]
  size = length
  member = elem
instance Ord k => Collection (k,v) (Map k v) where
  one = uncurry Map.singleton
  size = length
