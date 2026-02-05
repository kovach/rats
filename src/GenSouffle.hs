module GenSouffle
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
  PPI p i ts -> pp p <> args (pp i : map termCompile ts)
  p@(Pattern {}) -> error $ pp p
  Cmp op a b -> opString op <> pwrap (commas $ map tCompile [a,b])
  Eq a b -> termCompile a <> " = " <> termCompile b
  IsId t -> "isId" <> pwrap (termCompile t)
  Val a b -> "Val" <> args [termCompile a, termCompile b]
opString OpLt = "lt"
opString OpEq = "eq"
termCompile :: Term -> String
termCompile = \case
  TermVar v -> pp v
  TermPred pr -> cons "TermPred" [show $ pp pr]
  TermId i -> cons "TermId" [compileId i]
  TermFreshVar _ -> error ""
  TermChoiceVar (Just v) _ -> pp v
  TermChoiceVar Nothing _ -> error ""
  TermExt "$" -> cons "TermNum" ["autoinc()"]
  TermExt _ -> error "unhandled"
  v@TermBlank -> pp v
compileId (Id n vs) = cons "Id" [show n, toBinding vs]
toBinding [] = cons "Nil" []
toBinding (t:ts) = cons "Bind" [pp t, toBinding ts]
tCompile = \case
  L t -> cons "L" [termCompile t]
  R t -> cons "R" [termCompile t]
  Min a b -> cons "Min" (map tCompile [a,b])
  Max a b -> cons "Max" (map tCompile [a,b])
  Top -> cons "Top" []
cons s t = "$" <> s <> args t

chunkAtoms [] = ""
chunkAtoms xs =
  let (h,t) = splitAt 4 xs in
      case t of
        [] -> commas h
        _ -> commas h <> ",\n" <> chunkAtoms t

ruleCompile original (body, h) =
  let comment = "// " <> pp original <> "\n" in
  comment <>
    -- Souffle doesn't allow a rule with several heads and no body :)
    --   but, we don't currently typically generate these
    if Set.size body == 0 then
     unwords (map patternCompileDot $ Set.toList h)
    else
      chunkAtoms (map patternCompile $ Set.toList h)
      <> "\n  :-\n"
      <> chunkAtoms (map patternCompile $ Set.toList body)
      <> "\n."

schemaCompile :: [Pred] -> (Pred, Int) -> String
schemaCompile countPreds (p, arity) =
  ".decl " <> pp p <> args (map (\i -> "x" <> show i <> ":Term") [1..(arity+1)])
  <> (if p `elem` countPreds then "" else " .output " <> pp p)

readPrelude = do
  prelude <- readFile "prelude.dl"
  pure prelude
