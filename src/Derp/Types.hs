{-# LANGUAGE OverloadedStrings #-}
module Derp.Types where

import Data.Maybe
import Control.Monad hiding (join)
import Prelude hiding (take)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Aeson (ToJSON(..), Value(..), object, (.=))
import qualified Data.Aeson.Key as Key

import Basic
import qualified Binding as B
import qualified MMap
import MMap (MMap)

type Name = String
type Pred = String
data Id = Id { rule :: Name, bound :: [Term] }
  deriving (Show, Eq, Ord)
data Term
  = TermVar Name
  | TermPred Pred
  | TermNum Int
  | TermBlank
  | TermApp Name [Term]
  | TermString String
  deriving (Show, Eq, Ord)

type Tuple = [Term]

data E
  = Atom Tuple
  | NegAtom Tuple
  | Bind Term Term
  | Join E E
  | Unit
  deriving (Show, Eq, Ord)

pattern SpecialAtom p ts = Atom (TermPred ('#' : p) : ts)

newtype Tuples = Tuples (MMap.MMap Pred (Set Tuple))
  deriving (Semigroup, Monoid)

-- TODO: bdeps unused
data Binding = Binding { bind :: B.Binding Name Term, bdeps :: [Tuple] }
  deriving (Show, Eq, Ord)

-- TODO: remove this type
data Thunk = Thunk { tuples :: [Tuple], deps :: [Tuple] }
  deriving (Show, Eq, Ord)

data Closure a = Closure { context :: Binding, clVal :: a }
  deriving (Show, Eq, Ord, Functor)

type CE = Closure E

data Rule = Rule { body :: CE, head :: [Tuple] }
  deriving (Show, Eq, Ord)

instance Semigroup Binding where
  (Binding b1 d1) <> (Binding b2 d2) = Binding (b1 <> b2) (d1 <> d2)

instance Monoid Binding where
  mempty = Binding mempty none

instance PP Term where
  pp (TermVar v) = v
  pp (TermPred p) = p
  pp (TermNum i) = show i
  pp TermBlank = "_"
  pp (TermApp cons ts) = cons <> args (map pp ts)
  pp (TermString s) = show s

instance PP Id where
  pp (Id n vs) = n <> bwrap (unwords $ map pp vs)

instance Collection' Tuples where
  size (Tuples m) = sum $ map (\(_, vs) -> size vs) $ MMap.toList m

instance Collection Tuple Tuples where
  one (TermPred p : vs) = Tuples (MMap.singleton p (one vs))
  one _ = error ""
  member (TermPred p : vs) (Tuples m) = vs `member` MMap.lookup p m
  member _ _ = error ""
  pick (Tuples ts) = do
    ((p, vs), ts') <- pick ts
    pure (TermPred p : vs, Tuples ts')

instance PP Tuples where
  pp (Tuples m) = out
    where
      fix (k, vs) = map (TermPred k:) $ Set.toList vs
      --fix (k, vs) = map (TermPred k:) $ toTuples vs
      tuples = mconcat $ map fix $ MMap.toList m
      out = unlines . map pp $ tuples

instance ToJSON Term where
  toJSON (TermVar v)      = object ["tag" .= ("var" :: String), "name" .= v]
  toJSON (TermPred p)     = object ["tag" .= ("pred" :: String), "name" .= p]
  toJSON (TermNum i)      = object ["tag" .= ("num" :: String), "value" .= i]
  toJSON TermBlank        = object ["tag" .= ("blank" :: String)]
  toJSON (TermApp n ts)   = object ["tag" .= ("app" :: String), "name" .= n, "args" .= ts]
  toJSON (TermString s)   = object ["tag" .= ("string" :: String), "value" .= s]

instance ToJSON Tuples where
  toJSON (Tuples m) = object
    [ Key.fromString k .= map toJSON (Set.toList vs)
    | (k, vs) <- MMap.toList m ]

instance B.Unify Binding Term Term where
  unify b TermBlank _ = pure b
  unify b _ TermBlank = pure b
  unify (Binding b d) (TermVar var) v  = (\b' -> (Binding b' d)) <$> (B.unify b var v)
  unify b l@(TermPred _) r = guard (l == r) >> pure b
  unify b l@(TermNum _) r  = guard (l == r) >> pure b
  unify b l@(TermString _) r   = guard (l == r) >> pure b
  unify b (TermApp cons ts) (TermApp cons' ts') = do
    guard $ cons == cons'
    B.unify b ts ts'
  unify _ (TermApp {}) _ = fail "app"

instance B.Unify Binding [Term] [Term] where
  unify b x y = do
      go b x y
    where
      go c (t:ts) (v:vs) = do
        c' <- (B.unify c t v)
        go c' ts vs
      go c [] [] = pure c
      go _ _ _ = Nothing
