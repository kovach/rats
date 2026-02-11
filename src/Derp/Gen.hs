module Derp.Gen
  ( readPrelude, ruleCompile, ruleBlockCompile, schemaCompile )
  where

import Prelude hiding (pred, exp)
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad
import Data.Monoid (Sum(..))
import Data.List
import Data.Maybe
import Data.Functor.Identity
import Data.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace

import Basic
import Types
import Parser
import ParserCombinator
import MMap (MMap)

patternCompileDot = (<> ".") . patternCompile
patternCompile :: Pattern -> String
patternCompile = \case
  PPI p i ts -> spaces (pp p : pp i : map termCompile ts)
  p@(Pattern {}) -> error $ pp p
constraintCompile :: Constraint -> String
constraintCompile = \case
  Constraint p -> patternCompile p
  NegChose v -> "!" <> spaces [chosePred, varCompile v]
  Cmp op a b -> spaces [opString op, tCompile a, tCompile b]
  Eq a b -> spaces [termCompile a, "=", termCompile b]
  IsId t -> spaces ["isId", termCompile t]
  Val a b -> spaces ["val", termCompile a, termCompile b]
  Try (PPI p i ts) -> spaces [tryPred, cons (pp p) (pp i : termsCompile ts)]
  Try p -> error $ show p
opString OpLt = "lt"
opString OpEq = "eq"
varCompile = \case
  ExVar _ -> error "exvar in output"
  v -> pp v
termCompile :: Term -> String
termCompile = \case
  TermVar v -> varCompile v
  TermPred pr -> pp pr
  TermNum n -> show n
  TermId i -> idCompile i
  TermApp c ts -> cons c $ termsCompile ts
  TermFreshVar _ -> error ""
  TermChoiceVar (Just v) _ -> pp v
  TermChoiceVar Nothing _ -> error ""
  TermExt "$" -> "autoinc()"
  TermExt _ -> error "unhandled"
  v@TermBlank -> pp v
termsCompile = map termCompile
idCompile (Id n vs) = cons "id" [show n, toBinding vs]
toBinding [] = cons "nil" []
toBinding (t:ts) = cons "bind" [pp t, toBinding ts]
tCompile = \case
  L t -> cons "l" [termCompile t]
  R t -> cons "r" [termCompile t]
  Min a b -> cons "min" (map tCompile [a,b])
  Max a b -> cons "max" (map tCompile [a,b])
  Top -> cons "top" []
  Bot -> cons "bot" []
cons s t = s <> args t

chunkAtoms [] = ""
chunkAtoms xs =
  let (h,t) = splitAt 4 xs in
      case t of
        [] -> commas h
        _ -> commas h <> ",\n" <> chunkAtoms t

ruleBlockCompile (name, original) rules =
  let comment = "; " <> name <> ": " <> pp original <> "\n" in
  comment <> concatMap ruleCompile rules

ruleCompile (Rule body h) =
    chunkAtoms (map constraintCompile $ Set.toList body)
    <> "\n---\n"
    <> chunkAtoms (map constraintCompile $ Set.toList h)
    <> ".\n"

-- todo
schemaCompile :: [Pred] -> (Pred, Int) -> String
schemaCompile _ _ = ""

readPrelude = do
  prelude <- readFile "prelude.derp"
  pure prelude
