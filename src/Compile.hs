{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
module Compile (main1, main2, main3, runTest) where

import Prelude hiding (pred, exp, take)
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad
import Data.Monoid (Sum(..))
import Data.List hiding (take)
import qualified Data.List
import Data.Maybe
import Data.Functor.Identity
import Data.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import System.Process

import Basic
import Types
import qualified Parser as TP
import ParserCombinator (assertParse, lexComments)
import MMap (MMap)
import qualified MMap as M
import qualified Derp.Core as D
import qualified Derp.Parse as DP
import qualified GenSouffle as GS
import qualified Derp.Gen as GD

leftEnd t = L (TermVar t)
rightEnd t = R (TermVar t)

predPattern :: Pattern -> Maybe Pred
predPattern (PP p _) = Just p
predPattern _ = Nothing

patternVars (Pattern _ (PVar i _ _) ts) = maybeToList i <> termsVars ts
-- constraintVars: junk
termsVars = concatMap termVars
termVars (TermVar v) = [v]
termVars (TermChoiceVar _ v) = [v]
termVars (TermApp _ ts) = termsVars ts
termVars (TermFreshVar _) = [] -- these elaborate directly into an id constructor
termVars (TermId (Id _ vs)) = vs -- should be redundant
termVars (TermPred {}) = []
termVars (TermExt _) = []
termVars (TermNum _) = []
termVars TermBlank = []

freshAtomVar p | Just (Pred ('#':pr)) <- predPattern p = fresh $ capitalize pr
freshAtomVar p | Just (Pred pr) <- predPattern p = fresh $ capitalize pr
freshAtomVar _ = fresh "_id"

-- todo: negVars only
vars :: E -> [Var]
vars = nub . execWriter . eTraverse' go
  where
    go (Atom p) = tell (patternVars p)
    go (EVar t) = tell (termVars t)
    go _ = pure ()

negVars :: E -> [Var]
negVars = filter isNegVar . vars

posVars :: E -> [Var]
posVars = filter isPosVar . vars

patternBoundVars :: E -> [Var]
patternBoundVars = filter isNegVar . nub . execWriter . eTraverse' go
  where
    go (Atom (Pattern _ _ ts)) = tell (termsVars ts)
    go _ = pure ()

isBuiltin (TermPred (Pred ('#' : _)) : _) = True
isBuiltin _ = False

schema :: E -> [(Pred, Int)]
schema = execWriter . eTraverse' go
  where
    go (Atom (PP pr ts)) = do tell [(pr, length ts)]
    go _ = pure ()

-- todo: this should also sometimes yield PosVars
elabEVars e = eTraverse (pure . go) e
  where
    vs = map varName $ patternBoundVars e
    go (EVar (TermVar (NegVar v))) | not (v `elem` vs) = EVar (TermVar (ExVar v))
    go (EVar x) = trace ("!!! " <> show x<> " : " <> show vs) $ EVar x
    go x = x

elabCVars = eTermTraverse go
  where
    go (TermChoiceVar Nothing v) = do
      v' <- fresh (pp v)
      pure (TermChoiceVar (Just $ NegVar v') v)
    go e = pure e

elabNegAtoms ruleName e = eTraverse go e
  where
    go (Atom p@(Pattern AtomNeg NoVars ts)) = do
      m <- freshAtomVar p;
      let var = if isBuiltin ts then ExVar m else NegVar m
      pure $ Atom $ Pattern AtomNeg (AllVars var [] ruleName) ts
    go (Atom p@(Pattern AtomNeg _ ts)) = error ""
    go e' = pure e'

elabPosAtoms vs ruleName e = eTraverse go e
  where
    go (Atom p@(Pattern AtomPos NoVars ts)) = do
      m <- freshAtomVar p;
      pure $ Atom $ Pattern AtomPos (AllVars (PosVar m) vs ruleName) ts
    go (Atom p@(Pattern AtomAsk NoVars ts)) = do
      m <- freshAtomVar p;
      pure $ Atom $ Pattern AtomAsk (AllVars (PosVar m) vs ruleName) ts
    go (Atom p@(Pattern AtomPos _ ts)) = error ""
    go (Atom p@(Pattern AtomAsk _ ts)) = error ""
    go e' = pure e'

elabPosVars vs ruleName e = eTermTraverse go e
  where
    go (TermFreshVar v) = pure $ TermId $ Id (ruleName <> ":" <> pp v) vs
    go e' = pure e'

elab' r e = do
  -- mark existential variables,
  -- fresh names on choice vars,
  -- introduce bound variables
  e1 <- pure e >>= elabEVars >>= elabCVars >>= elabNegAtoms r
  let vs = negVars e1
  -- introduce fresh ids that capture the negVars for
  --   positive atoms, and
  --   `TermFreshVar` instances
  elabPosAtoms vs r e1
    >>= elabPosVars vs r

elab :: (Name, E) -> E
elab = evalM . uncurry elab'

type MonadPatternWriter m = MonadWriter [Constraint] m

checkTerm :: MonadPatternWriter m => Term -> m ()
checkTerm = \case
  TermChoiceVar (Just v') v ->
    tell [Val (TermVar v') (TermVar v)]
  _ -> pure ()

-- todo
conAtom v = (I a b, [a `Lt` b]) where a = leftEnd v; b = rightEnd v
conOver (I al ar) (I bl br) = (I al ar, [al `Lt` bl, br `Lt` ar])
conSame (I al ar) (I bl br) = (I al ar, [al `Eql` bl, br `Eql` ar])
conAnd (I al ar) (I bl br) =
  ( I (Max al bl) (Min ar br)
  , [Max al bl `Lt` Min ar br])

check :: MonadPatternWriter m => E -> m I
check (Atom p@(Pattern AtomNeg (AllVars v@(ExVar _) _ _) ts)) | isBuiltin ts = do
  mapM_ checkTerm ts
  tell [Constraint p]
  pure (I (leftEnd v) (rightEnd v))
check (Atom (Pattern AtomNeg (AllVars _ _ _) ts)) | isBuiltin ts = error ""
check (Atom p@(Pattern sign (AllVars v vs name) ts)) = do
  mapM_ checkTerm ts
  case sign of
    AtomPos -> do
      tell [Constraint p, (leftEnd v) `Lt` (rightEnd v)]
      let i = TermId $ Id (name <> ":__" <> pp v) vs
      tell [Eq (TermVar v) i, IsId (TermVar v)]
    AtomNeg -> do
      tell [Constraint p, (leftEnd v) `Lt` (rightEnd v)]
    AtomAsk -> do
      tell [Try p, (leftEnd v) `Lt` (rightEnd v)]
      let i = TermId $ Id (name <> ":__" <> pp v) vs
      tell [Eq (TermVar v) i, IsId (TermVar v)]
  pure (I (leftEnd v) (rightEnd v))
check (EVar t) = do
  tell [L t `Lt` R t]
  pure $ I (L t) (R t)
check (Atom p) = error $ pp p
-- check (Atom p) = error $ pp p
check (After e) = do
  I _ ar <- check e
  pure $ I ar Top
check (Par a b) = do
  I al ar <- check a
  I bl br <- check b
  pure $ I (Min al bl) (Max ar br)
check (And a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [Max al bl `Lt` Min ar br]
  pure $ I (Max al bl) (Min ar br)
check (At a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [al `Lt` bl, bl `Lt` ar]
  pure $ I bl br
check (Seq a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [ar `Lt` bl]
  pure $ I al br
check (Over a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [al `Lt` bl, br `Lt` ar]
  pure $ I al ar
check (Under a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [bl `Lt` al, ar `Lt` br]
  pure $ I al ar
check (Same a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [al `Eql` bl, br `Eql` ar]
  pure $ I al ar

checkAll :: E -> [Constraint]
checkAll = snd . runWriter . check

-- expand and simplify constrains:
expandConstraint :: Constraint -> [Constraint]
expandConstraint (Cmp op (Max a b) c) | opIneq op = expandConstraints [Cmp op a c, Cmp op b c]
expandConstraint (Cmp op a (Min b c)) | opIneq op = expandConstraints [Cmp op a b, Cmp op a c]
expandConstraint (Cmp OpEq a a') | a == a' = []
expandConstraint (Cmp _ _ Top) = []
-- expandConstraint p@(Cmp _ (Min _ _) _) = error $ pp p  -- no disjunctive comparisons
-- expandConstraint p@(Cmp _ _ (Max _ _)) = error $ pp p  -- no disjunctive comparisons
expandConstraint x = [x]

expandConstraints :: [Constraint] -> [Constraint]
expandConstraints = concatMap expandConstraint

-- TODO: handle min, max in terms
quantElimConstraints vs ps = out
  where
    chk c x = if c then x else error ""
    out' = nub $ rest <> elimAll <> elimEx
    out = chk c out'
    c = all ok out'
    ok (Cmp _ a b) = not (a `elem` exVars || b `elem` exVars)
    ok _ = True
    (cmps, rest) = partition isCmp ps
    elimEx = elimVars exVars cmps
    elimAll = elimVars posVars elimEx
    exVars = concatMap (\v -> [leftEnd v, rightEnd v]) $ filter isExVar vs
    posVars = concatMap (\v -> [leftEnd v, rightEnd v]) $ filter isPosVar vs
    isGt v (Cmp OpLt _ v') = v == v'
    isGt _ _ = False
    isLt v (Cmp OpLt v' _) = v == v'
    isLt _ _ = False
    isEq v (Cmp OpEq a b) | v == a && v /= b = Just b
    isEq v (Cmp OpEq a b) | v == b && v /= a = Just a
    isEq _ _ = Nothing
    isCmp (Cmp {}) = True
    isCmp _ = False
    isOther v (Cmp _ a b) = a /= v && b /= v
    byCmp v cmps = (ltx, xlt, xeq)
      where
        ltx = filter (isGt v) cmps
        xlt = filter (isLt v) cmps
        xeq = mapMaybe (isEq v) cmps
    subst1 v x v' = if v == v' then x else v'
    substCmp v x (Cmp op a b) = Cmp op (subst1 v x a) (subst1 v x b)
    subst v x cmps = map (substCmp v x) cmps
    cross ltx xlt = [ Lt a b | Lt a _ <- ltx, Lt _ b <- xlt ]
    elimVar v cmps =
      case xeq of
        x : _ -> subst v x cmps
        [] -> other <> cross ltx xlt
      where
        (ltx, xlt, xeq) = byCmp v cmps
        other = filter (isOther v) cmps
    elimVars vs cmps = foldr elimVar cmps vs

termContainsId vs (TermVar v) = v `elem` vs
termContainsId _ _ = False

tContainsId vs = \case
  L t' -> termContainsId vs t'
  R t' -> termContainsId vs t'
  Min t1 t2 -> tContainsId vs t1 || tContainsId vs t2
  Max t1 t2 -> tContainsId vs t1 || tContainsId vs t2
  Top -> False
  Bot -> False

isPos _ (Constraint (Pattern AtomPos _ _)) = True
isPos _ (Constraint (Pattern{})) = False
isPos _ (Eq _ _) = False
isPos _ (Val _ _) = False
isPos vs (Cmp _ a b) = any (tContainsId vs) [a,b]
isPos vs (IsId t) = termContainsId vs t
isPos _ (Try _) = True

splitConstraints :: [Var] -> [Constraint] -> Rule
splitConstraints pvs x =
  let (pos, neg) = partition (isPos pvs) x
   in Rule (Set.fromList neg) (Set.fromList pos)

type Constraints = Set Constraint

depVarSet :: Constraints -> Var -> [Term] -> Set Var
depVarSet cs v2 ts = Set.unions (Set.map tBefore cs) <> vBefore
  where
    tBefore (Cmp OpLt (L (TermVar v1)) (L (TermVar v2'))) | v2 == v2' = one v1
    -- TODO eq
    tBefore _ = none

    vs = termsVars ts
    vBefore = Set.unions . Set.map binders $ cs
    binders (Constraint (Pattern AtomNeg (PVar (Just v) _ _) ts')) =
      if not . null $ intersect (termsVars ts') vs then one v else none
    binders _ = none

-- Compute transitive closure of a set of constraints with respect to equality and inequality
saturate :: Constraints -> Constraints
saturate = fixpoint step
  where
    isLt (Cmp OpLt a b) = Just (a, b)
    isLt _ = Nothing
    isEq (Cmp OpEq a b) = Just (a, b)
    isEq _ = Nothing

    step cs =
      let lts    = mapMaybe isLt (Set.toList cs)
          eqs    = mapMaybe isEq (Set.toList cs)
          symEqs = eqs ++ [(b, a) | (a, b) <- eqs]
          -- transitivity of <: a < b, b < c => a < c
          new1   = [Cmp OpLt a c | (a, b) <- lts,    (b', c) <- lts,    b == b']
          -- eq substitution in < (left): a = b, a < x => b < x
          new2   = [Cmp OpLt b x | (a, b) <- symEqs, (a', x) <- lts,    a == a']
          -- eq substitution in < (right): a = b, x < a => x < b
          new3   = [Cmp OpLt x b | (a, b) <- symEqs, (x, a') <- lts,    a == a']
          -- transitivity of =: a = b, b = c => a = c
          new4   = [Cmp OpEq a c | (a, b) <- symEqs, (b', c) <- symEqs, b == b']
      in cs <> Set.fromList (new1 <> new2 <> new3 <> new4)

    fixpoint f x = let x' = f x in if size x' == size x then x else fixpoint f x'

-- TODO: merging
depVarSets :: [Constraint] -> [(Var, Set Var)]
depVarSets cs = [ (v, depVarSet cs' v ts) | (v, ts) <- mapMaybe findPos $ cs ]
  where
    cs' = saturate $ Set.fromList cs
    findPos (Constraint (Pattern AtomPos (PVar (Just v) _ _) ts)) = Just (v, ts)
    -- TODO AtomAsk?
    findPos _ = Nothing

generateConstraints :: E -> Rule
generateConstraints e = trace (unlines $ map pp c') $ out
  where
    out = splitConstraints (posVars e) c
    c' = depVarSets c
    c = expandConstraints
        . quantElimConstraints (vars e)
        . expandConstraints
        . checkAll $ e

ppt f cs = trace ("!!: " <> unlines (map pp cs)) $ f cs
generateConstraints' e = splitConstraints (posVars e)
  . (ppt expandConstraints)
  . (ppt $ quantElimConstraints (vars e))
  . expandConstraints
  . checkAll $ e

compileExp :: (Name, E) -> [Rule]
compileExp pr@(_, _) = one r <> tryPatterns
  where
    r@(Rule _ h) = generateConstraints . elab $ pr
    tryPatterns = mapMaybe fixTry $ Set.toList h
    fixTry (Try p) = Just $ Rule b' h'
      where
        p' = freshPattern p
        b' = Set.fromList $ [Try p', NegChose x]
        h' = Set.fromList $ [Constraint p']
    fixTry _ = Nothing
    x = NegVar "X"
    freshPattern (Pattern sign (AllVars _ ds n) (p : vs)) =
      Pattern sign (AllVars x ds n) ts'
        where
          ts' = p : (map (\i -> TermVar $ NegVar $ "X" <> show i) [1.. length vs])
    freshPattern _ = error ""

-- todo:
--
compile :: [Statement] -> String
compile ps = result
  where
    (ops, es) = partitionEithers $ map isOp ps
    isOp (Pragma p) = Left p
    isOp (RuleStatement (Just n) e) = Right (n,e)
    isOp (RuleStatement Nothing _) = error ""
    notBasic (pr, _) = not (pr `elem` map Pred ["move", "at"])
    sch = filter notBasic $ nub $ concatMap (schema . snd) es
    result = unlines $
      map (GD.schemaCompile ops) sch
      <> map (\e -> GD.ruleBlockCompile e (compileExp e)) es

mkFile path p = do
  prelude <- GD.readPrelude
  writeFile path $ prelude <> p

demo name rules = do
    case find (byName) rules of
      Just (RuleStatement _ r) -> do
        let f = (name, r)
        --let f = (name, fromJust $ lookup name rules)
        pprint $ snd f
        putStrLn "~~~~~~~~~"
        let f' = elab f
        pprint f'
        putStrLn "~~~~~~~~~"
        let Rule body h = generateConstraints' f' -- todo
        mapM_ pprint body
        putStrLn "---------"
        mapM_ pprint h
        putStrLn "~~~~~~~~~"
      _ -> error ""
  where
    byName (RuleStatement (Just n) _) | n == name = True
    byName _ = False

genDerp base = do
  pr0 <- readFile (base ++ ".turn")
  let ttt = TP.parse pr0
  let name _ r@(RuleStatement (Just _) _) = r
      name n (RuleStatement Nothing r) = RuleStatement (Just n) r
      name _ x = x
  let rules = zipWith name [ "r" <> show i | i <- [1..] ] ttt
  let ruleText = compile rules
  prelude <- GD.readPrelude
  let result = prelude <> ruleText
  pure (result, ruleText)

main1 :: String -> IO String
main1 base = do
  (result, ruleText) <- genDerp base
  putStrLn $ "generated derp:\n" <> ruleText
  writeFile (base ++ ".derp") result
  pure result

main2' input = do
  let rs = DP.parse input -- assertParse prog $ lexComments ";" input
  -- print rs
  let D.Tuples ts = D.iterRules none rs
      hide :: [String] = []
      --hide :: [String] = ["le", "lt"]
      out' = D.Tuples $ M.filterWithKey (\k _ -> not (k `member` hide)) ts
  putStrLn "\nresult:"
  pprint $ out'
  print $ size out'
  putStrLn "."
  pure out'

-- todo
main4 = do
  r1 <- TP.parse <$> readFile "ttt.turn"
  layout <- DP.parse <$> readFile "layout.derp"
  pure ()

main2 = do
  --input <- readFile "test.derp"
  input <- readFile "layout.derp"
  main2' input

main3 = do
  str <- main1 "ttt"
  main2' str

runTest base = do
  (result, rules) <- genDerp base
  writeFile "tmp.derp" result
  putStrLn rules
  --(_, df, _) <- readProcessWithExitCode "diff" ["expected.derp", "tmp.derp"] ""
  --putStrLn  df
