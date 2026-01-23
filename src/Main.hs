{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
module Main (main) where

import Prelude hiding (pred, exp)
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad
import Data.Monoid (Sum(..))
import Data.Maybe
import Data.Functor.Identity
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Types
import Parser
import ParserCombinator
import MMap (MMap)

-- todo
-- type MonadComp m = (MonadPatternWriter m, MonadFreshVarState m)
-- type MC a = WriterT [Pattern] (State (MMap String (Sum Int))) a

pattern P p i ts = IdPattern i (TermPred p : ts)

leftEnd (TermAfter t) = rightEnd t
leftEnd t = L t
rightEnd (TermAfter _) = Top
rightEnd t = R t

predString (Pred s) = s
predPattern :: Pattern -> Maybe Pred
predPattern (Pattern _ (TermPred p : _)) = Just p
predPattern _ = Nothing
pVars (Pattern _ ts) = varTerms ts
pVars (IdPattern i ts) = varTerms (i:ts)
pVars (Cmp _ a b) = tVars a <> tVars b
varTerms = concatMap termVars
termVars (TermVar v) = [v]
termVars (TermId (Id _ vs)) = vs
termVars _ = []
tVars (L t) = termVars t
tVars (R t) = termVars t
tVars (Min a b) = tVars a <> tVars b
tVars (Max a b) = tVars a <> tVars b
tVars Top = []

pattern Lt a b = Cmp OpLt a b
pattern Le a b = Cmp OpLe a b
pattern IdAtom i ts = Atom (IdPattern i ts)

eTraverse :: Applicative m => (Pattern -> m E) -> E -> m E
eTraverse f = go
  where
    go (Atom p) = f p
    go (And a b) = And <$> (go a) <*> (go b)
    go (Seq a b) = Seq <$> (go a) <*> (go b)
    go (Par a b) = Par <$> (go a) <*> (go b)
    go (Over a b) = Over <$> (go a) <*> (go b)

eFoldM :: Monad m => (E -> m E) -> E -> m E
eFoldM f = go
  where
    go a@(Atom{}) = f a
    go (And a b)  = do a' <- go a; b' <- go b; f $ And a' b'
    go (Seq a b)  = do a' <- go a; b' <- go b; f $ Seq a' b'
    go (Par a b)  = do a' <- go a; b' <- go b; f $ Par a' b'
    go (Over a b) = do a' <- go a; b' <- go b; f $ Over a' b'

-- emap :: (E -> E) -> E -> E
-- emap f = runIdentity . eFoldM (pure . f)

negUnary x = Atom (Pattern AtomDuring [TermPred (Pred x)])
posUnary x = Atom (Pattern AtomPos [TermPred (Pred x)])

freshAtomVar p | Just pr <- predPattern p = fresh $ capitalize $ predString pr
freshAtomVar _ = fresh "_id"

vars :: E -> [Var]
vars = snd . runWriter . eTraverse go
  where
    go p = do tell (pVars p); pure (Atom p)

elabNeg = eTraverse go
  where
    go (p@(Pattern AtomDuring ts)) = do
      m <- freshAtomVar p; pure $ Atom (IdPattern (TermVar (Var m)) ts)
    go (p@(Pattern AtomAfter ts)) = do
      m <- freshAtomVar p; pure $ Atom (IdPattern (TermAfter $ TermVar (Var m)) ts)
    go p = pure (Atom p)

elabPos ruleName e = eTraverse go e
  where
    vs = vars e
    go p@(Pattern AtomPos ts) = do
      m <- freshAtomVar p;
      let i = Id (ruleName <> ":" <> m) vs
      pure (IdAtom (TermId i) ts)
    go p = pure (Atom p)

type Rule = (Name, E)

elab r = elabNeg >=> elabPos r
runElab = evalM . uncurry elab
elabAll :: [Rule] -> [E]
elabAll = evalM . mapM (uncurry elab)

type MonadPatternWriter m = MonadWriter [Pattern] m

check :: MonadPatternWriter m => E -> m I
check (Atom p@(IdPattern i _)) = do
  tell [p, Lt (leftEnd i) (rightEnd i)];
  pure (I (leftEnd i) (rightEnd i))
check (Atom p) = error $ pp p
check (Par a b) = do
  I al ar <- check a
  I bl br <- check b
  pure $ I (Min al bl) (Max ar br)
check (And a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [Max al bl `Lt` Min ar br]
  pure $ I (Max al bl) (Min ar br)
check (Seq a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [ar `Le` bl]
  pure $ I al br
check (Over a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [al `Lt` bl, br `Lt` ar]
  pure $ I al br

checkAll :: E -> [Pattern]
checkAll = snd . runWriter . check

-- expand and simplify constrains:
expandConstraint :: Pattern -> [Pattern]
expandConstraint (Cmp op (Max a b) c) = expandConstraints [Cmp op a c, Cmp op b c]
expandConstraint (Cmp op a (Min b c)) = expandConstraints [Cmp op a b, Cmp op a c]
expandConstraint (Cmp _ _ Top) = []
expandConstraint p@(Cmp _ (Min _ _) _) = error $ pp p  -- no disjunctive comparisons
expandConstraint p@(Cmp _ _ (Max _ _)) = error $ pp p  -- no disjunctive comparisons
expandConstraint x = [x]

expandConstraints :: [Pattern] -> [Pattern]
expandConstraints = concatMap expandConstraint

termContainsId (TermId _) = True
termContainsId _ = False
tContainsId = \case
  L t' -> termContainsId t'
  R t' -> termContainsId t'
  Min t1 t2 -> tContainsId t1 || tContainsId t2
  Max t1 t2 -> tContainsId t1 || tContainsId t2
  Top -> False

isPos :: Pattern -> Bool
isPos (IdPattern i ts) = any termContainsId (i:ts)
isPos (Cmp _ a b) = any tContainsId [a,b]
isPos (IsId t) = termContainsId t
isPos (Pattern {}) = error ""

splitConstraints x =
  let (pos, neg) = partition isPos x
   in (Set.fromList neg, Set.fromList pos)

chk = splitConstraints . expandConstraints . checkAll

compile ps =
  let ps' = ps
  in map (ruleCompile . chk . runElab) ps'

commas = intercalate ", "
args = pwrap . intercalate ", "
ruleCompile (body, h) =
  if Set.size body == 0 then
   unwords (map patternCompile1 $ Set.toList h)
  else
    commas (map patternCompile $ Set.toList h)
    <> "\n  :-\n"
    <> commas (map patternCompile $ Set.toList body)
    <> "\n."

patternCompile1 = (<> ".") . patternCompile
patternCompile :: Pattern -> String
patternCompile = \case
  P p i ts -> pp p <> args (map termCompile $ i : ts)
  IdPattern _ _ -> error ""
  Cmp op a b -> opString op <> pwrap (commas $ map tCompile [a,b])
  IsId t -> "IsId" <> pwrap (termCompile t)
  Pattern {} -> error ""
opString OpLt = "Lt"
opString OpLe = "Le"
termCompile :: Term -> String
termCompile = \case
  TermVar v -> pp v -- !
  TermPred pr -> cons "TermPred" [pp pr]
  TermId i -> cons "TermId" [compileId i]
  TermAfter t -> termCompile t
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

mkFile path p = do
  prelude <- readFile "prelude.dl"
  writeFile path $ prelude <> p

exp = assertParse expr

--
-- Example:
-- `a` and 2 `b`s that overlap:
e_ab = assertParse expr "!a, !b, !b" -- ands [posUnary "a", posUnary "b", posUnary "b"]
-- an `a` that encloses `a` b:
e_ab' = assertParse expr "!a / !b" -- Over (posUnary "a") (posUnary "b")
-- within every `a`,`b` overlap, do (`c`, then `d`):
e_cd = assertParse expr "?a, ?b / !c | !d"

-- End state: three `c` and `d` episodes.
--

rules =
  [ ("r", e_cd)
  , ("ab", e_ab)
  , ("a/b", e_ab')
  , ("foo", exp ">d, !e")
  ]

demo name = do
  let f = (name, fromJust $ lookup name rules)
  pprint $ snd f
  putStrLn "~~~~~~~~~"
  let [f'] = elabAll [f]
  pprint f'
  putStrLn "~~~~~~~~~"
  let (body, h) = chk f'
  mapM_ pprint body
  putStrLn "---------"
  mapM_ pprint h
  putStrLn "~~~~~~~~~"

main = do
  demo "foo"

  let result = unlines $ compile rules
  mkFile "out.dl" $ result
