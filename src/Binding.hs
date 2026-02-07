{-# LANGUAGE FunctionalDependencies #-}
module Binding where

import Prelude hiding ( lookup )
import qualified Prelude ( lookup )
import qualified Prelude as P
import Control.Monad
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map

import Basic
import Types

data Binding k v = Binding { mapping :: [(k,v)] }
  deriving (Show, Eq, Ord)

empty :: Binding k v
empty = Binding mempty

ofList :: Ord k => [(k,v)] -> Binding k v
ofList = Binding

extend :: Ord k => Binding k v -> k -> v -> Binding k v
extend (Binding s) v x = Binding ((v,x):s)

tryExtend :: (Ord k, Eq v) => Binding k v -> k -> v -> Maybe (Binding k v)
tryExtend b var v
  | Just l <- lookup var b = guard (l == v) >> pure b
tryExtend b var v          = pure (extend b var v)

instance Ord k => Semigroup (Binding k v) where
  (Binding as) <> (Binding bs) = Binding (as <> bs)

instance Ord k => Monoid (Binding k v) where
  mempty = Binding.empty

merge :: (Ord k, Eq v) => Binding k v -> Binding k v -> Maybe (Binding k v)
merge a (Binding bs) = foldM (\a' (k,v) -> tryExtend a' k v) a bs

lookup :: Ord k => k -> Binding k v -> Maybe v
lookup k (Binding bs) = Prelude.lookup k bs

instance (PP k, PP v) => PP (Binding k v) where
  pp (Binding bs) =
    intercalate " / " $
      map (\(k, v) -> pp k <> " " <> pp v) bs

class Unify bind a b | a b -> bind where
  unify :: bind -> a -> b -> Maybe bind

instance Eq v => Unify (Binding Name v) Name v where
  unify = tryExtend
