{-# LANGUAGE AllowAmbiguousTypes #-}

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
spaces = intercalate " "
args = pwrap . intercalate ", "

assert a b | a == b = putStrLn "ok"
assert a b = error $ "not-equal:\n" <> pp a <> "\n\n" <> pp b

class Monoid b => Collection' b where
  none :: b
  none = mempty
  size :: b -> Int
class (Collection' b, Monoid b) => Collection a b where
  one :: a -> b
  ofList :: [a] -> b
  ofList = mconcat . map one
  member :: a -> b -> Bool
  take :: b -> Maybe (a, b)
instance Ord a => Collection a (Set a) where
  one = Set.singleton
  member = elem
  take = Set.minView
instance Ord a => Collection' (Set a) where
  size = length
instance Eq a => Collection' [a] where
  size = length
instance Eq a => Collection a [a] where
  one x = [x]
  member = elem
  take = \case
    a:as -> Just (a,as)
    [] -> Nothing
instance Ord k => Collection' (Map k c) where
  size = length
instance (Ord k, Collection v c) => Collection (k, v) (Map k c) where
  one (k, v) = Map.singleton k (one v)
  take m = do
    ((k,c), m') <- Map.minViewWithKey m
    (v,c') <- Basic.take c
    pure ((k,v), m' <> Map.singleton k c')
  member (k, v) m =
    case Map.lookup k m of
      Just c -> v `member` c
      _ -> False
