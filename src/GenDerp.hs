module GenDerp
  ( readPrelude, ruleCompile, schemaCompile )
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
  Cmp op a b -> spaces $ opString op : map tCompile [a,b]
  Eq a b -> termCompile a <> " = " <> termCompile b
  IsId t -> "isId" <> " " <> termCompile t
  Val a b -> spaces $ "Val" : [termCompile a, termCompile b]
opString OpLt = "lt"
opString OpEq = "eq"
termCompile :: Term -> String
termCompile = \case
  TermVar (ExVar _) -> error "exvar in output"
  TermVar v -> pp v
  TermPred pr -> pp pr
  TermNum n -> show n
  TermId i -> compileId i
  TermFreshVar _ -> error ""
  TermChoiceVar (Just v) _ -> pp v
  TermChoiceVar Nothing _ -> error ""
  TermExt "$" -> "autoinc()"
  TermExt _ -> error "unhandled"
  v@TermBlank -> pp v
compileId (Id n vs) = cons "id" [show n, toBinding vs]
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

ruleCompile (name, original) (body, h) =
  let comment = "; " <> name <> ": " <> pp original <> "\n" in
  comment <>
    -- Souffle doesn't allow a rule with several heads and no body :)
    --   but, we don't currently typically generate these
    if Set.size body == 0 then
     unwords (map patternCompileDot $ Set.toList h)
    else
      chunkAtoms (map patternCompile $ Set.toList body)
      <> "\n---\n"
      <> chunkAtoms (map patternCompile $ Set.toList h)
      <> ".\n"

-- todo
schemaCompile :: [Pred] -> (Pred, Int) -> String
schemaCompile _ _ = ""

readPrelude = do
  prelude <- readFile "prelude.derp"
  pure prelude
