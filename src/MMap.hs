module MMap
  ( MMap
  , keys
  , mapWithKey
  , empty
  , singleton
  , null
  , toList
  , fromList
  , fromListWithKey
  , lookup
  , insert
  )
where

import Prelude hiding (null, lookup)
import Data.Maybe
import qualified Data.Map as M

newtype MMap k v = MMap (M.Map k v)
  deriving (Show, Eq, Ord)

insert' :: (Ord k, Semigroup v) => k -> v -> M.Map k v -> M.Map k v
insert' k v m = M.alter (\case
  Nothing -> Just v
  Just v' -> Just $ v' <> v) k m

insertWithKey :: (Ord k) => (k -> v -> v -> v) -> k -> v -> M.Map k v -> M.Map k v
insertWithKey f k v m = M.alter (\case
  Nothing -> Just v
  Just v' -> Just $ f k v' v) k m

instance (Ord k, Semigroup v) => Semigroup (MMap k v) where
  (MMap a) <> (MMap b) = MMap $ M.foldrWithKey insert' a b
instance (Ord k, Semigroup v) => Monoid (MMap k v) where
  mempty = MMap M.empty

keys (MMap m) = M.keys m
mapWithKey f (MMap m) = M.mapWithKey f m
foldlWithKey' f a (MMap m) = M.foldlWithKey' f a m
empty = MMap M.empty
singleton k v = MMap $ M.singleton k v
null (MMap m) = M.null m
toList (MMap m) = M.toList m

-- Differences in type or behavior from standard Map interface --
fromList :: (Ord k, Semigroup v) => [(k, v)] -> MMap k v
fromList = MMap . foldr (uncurry insert') M.empty

fromListWithKey :: (Ord k, Semigroup v) => (k -> v -> v -> v) -> [(k, v)] -> MMap k v
fromListWithKey f = MMap . foldr (uncurry (insertWithKey f)) M.empty

lookup :: (Ord k, Monoid v) => k -> MMap k v -> v
lookup k (MMap m) = fromMaybe mempty $ M.lookup k m

insert :: (Ord k, Semigroup v) => k -> v -> MMap k v -> MMap k v
insert k v (MMap m) = MMap (insert' k v m)
-- end --
