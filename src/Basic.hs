{-# LANGUAGE AllowAmbiguousTypes #-}

module Basic where

import Prelude hiding (take)
import Data.Char
import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified MMap as MMap
import MMap (MMap)

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

class Monoid b => Collection' b where
  none :: b
  none = mempty
  size :: b -> Int
  isEmpty :: b -> Bool
  isEmpty = (== 0) . size

class (Collection' b, Monoid b) => Collection a b where
  one :: a -> b
  ofList :: [a] -> b
  ofList = mconcat . map one
  member :: a -> b -> Bool
  pick :: b -> Maybe (a, b)

instance Eq a => Collection' [a] where
  size = length
  isEmpty = null
instance Eq a => Collection a [a] where
  one x = [x]
  member = elem
  pick = \case
    a:as -> Just (a,as)
    [] -> Nothing

instance Ord a => Collection' (Set a) where
  size = length
  isEmpty = isNothing . Set.minView

instance Ord a => Collection a (Set a) where
  one = Set.singleton
  member = elem
  pick = Set.minView

instance Ord k => Collection' (Map k c) where
  size = length
  isEmpty = isNothing . Map.minView

instance (Ord k, Collection v c) => Collection (k, v) (Map k c) where
  one (k, v) = Map.singleton k (one v)
  pick m = do
    ((k,c), m') <- Map.minViewWithKey m
    (v,c') <- pick c
    pure ((k,v), m' <> Map.singleton k c')
  member (k, v) m =
    case Map.lookup k m of
      Just c -> v `member` c
      _ -> False

instance (Ord k, Semigroup c) => Collection' (MMap k c) where
  size = size
  isEmpty = isNothing . MMap.minViewWithKey

instance (Ord k, Collection v c) => Collection (k, v) (MMap k c) where
  one (k, v) = MMap.singleton k (one v)
  pick m = do
    ((k,c), m') <- MMap.minViewWithKey m
    (v,c') <- pick c
    pure ((k,v), m' <> MMap.singleton k c')
  member (k, v) m = v `member` MMap.lookup k m

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

mconcatMap f = mconcat . map f

(.>) = flip (.)
