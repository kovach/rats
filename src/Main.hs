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
import Data.List
import Data.Maybe
import Data.Functor.Identity
import Data.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace

import Basic
import Types
import Parser (program)
import ParserCombinator
import MMap (MMap)
import qualified Derp as D
import ParseDerp
import qualified GenSouffle as GS
import qualified GenDerp as GD

leftEnd t = L (TermVar t)
rightEnd t = R (TermVar t)

predPattern :: Pattern -> Maybe Pred
predPattern (PP p _) = Just p
predPattern _ = Nothing

patternVars (Pattern _ PVar0 ts) = termsVars ts
patternVars (Pattern _ (PVar2 i _ _) ts) = i : termsVars ts
patternVars (Cmp _ a b) = tVars a <> tVars b
patternVars (IsId t) = termVars t
patternVars (Eq a b) = termVars a <> termVars b
patternVars (Val a b) = termVars a <> termVars b
termsVars = concatMap termVars
termVars (TermVar v) = [v]
termVars (TermChoiceVar _ v) = [v]
termVars (TermFreshVar _) = [] -- these elaborate directly into an id constructor
termVars (TermId (Id _ vs)) = vs -- should be redundant
termVars (TermPred {}) = []
termVars (TermExt _) = []
termVars (TermNum _) = []
termVars TermBlank = []
tVars (L t) = termVars t
tVars (R t) = termVars t
tVars (Min a b) = tVars a <> tVars b
tVars (Max a b) = tVars a <> tVars b
tVars Top = []

pattern Lt a b = Cmp OpLt a b
pattern Eql a b = Cmp OpEq a b

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
    go (Atom p@(Pattern AtomNeg PVar0 ts)) = do
      m <- freshAtomVar p;
      let var = if isBuiltin ts then ExVar m else NegVar m
      pure $ Atom $ Pattern AtomNeg (PVar2 var [] ruleName) ts
    go e' = pure e'

elabPosAtoms vs ruleName e = eTraverse go e
  where
    go (Atom p@(Pattern AtomPos PVar0 ts)) = do
      m <- freshAtomVar p;
      pure $ Atom $ Pattern AtomPos (PVar2 (PosVar m) vs ruleName) ts
    go e' = pure e'

elabPosVars vs ruleName e = eTermTraverse go e
  where
    go (TermFreshVar v) = pure $ TermId $ Id (ruleName <> ":" <> pp v) vs
    go e' = pure e'

type Rule = (Name, E)

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

type MonadPatternWriter m = MonadWriter [Pattern] m

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
check (Atom p@(Pattern AtomNeg (PVar2 v@(ExVar _) _ _) ts)) | isBuiltin ts = do
  mapM_ checkTerm ts
  tell [p]
  pure (I (leftEnd v) (rightEnd v))
check (Atom (Pattern AtomNeg (PVar2 _ _ _) ts)) | isBuiltin ts = error ""
check (Atom p@(Pattern sign (PVar2 v vs name) ts)) = do
  mapM_ checkTerm ts
  tell [p, (leftEnd v) `Lt` (rightEnd v)]
  case sign of
    AtomPos -> do
      let i = TermId $ Id (name <> ":__" <> pp v) vs
      tell [Eq (TermVar v) i, IsId (TermVar v)]
    _ -> pure ()
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

checkAll :: E -> [Pattern]
checkAll = snd . runWriter . check

-- expand and simplify constrains:
expandConstraint :: Pattern -> [Pattern]
expandConstraint (Cmp op (Max a b) c) | opIneq op = expandConstraints [Cmp op a c, Cmp op b c]
expandConstraint (Cmp op a (Min b c)) | opIneq op = expandConstraints [Cmp op a b, Cmp op a c]
expandConstraint (Cmp OpEq a a') | a == a' = []
expandConstraint (Cmp _ _ Top) = []
-- expandConstraint p@(Cmp _ (Min _ _) _) = error $ pp p  -- no disjunctive comparisons
-- expandConstraint p@(Cmp _ _ (Max _ _)) = error $ pp p  -- no disjunctive comparisons
expandConstraint x = [x]

expandConstraints :: [Pattern] -> [Pattern]
expandConstraints = concatMap expandConstraint

foo = \case
  x | x > 0 -> 1
  x | x < 0 -> 2

-- TODO: handle min, max in terms
quantElimConstraints vs ps = trace ("evs: " <> pp exVars) out
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

isPos _ (Pattern AtomPos _ _) = True
isPos _ (Pattern{}) = False
isPos _ (Eq _ _) = False
isPos _ (Val _ _) = False
isPos vs (Cmp _ a b) = any (tContainsId vs) [a,b]
isPos vs (IsId t) = termContainsId vs t

splitConstraints :: [Var] -> [Pattern] -> (Set Pattern, Set Pattern)
splitConstraints pvs x =
  let (pos, neg) = partition (isPos pvs) x
   in (Set.fromList neg, Set.fromList pos)

generateConstraints e = splitConstraints (posVars e)
  . expandConstraints
  . quantElimConstraints (vars e)
  . expandConstraints
  . checkAll $ e

ppt f cs = trace ("!!: " <> unlines (map pp cs)) $ f cs
generateConstraints' e = splitConstraints (posVars e)
  . (ppt expandConstraints)
  . (ppt $ quantElimConstraints (vars e))
  . expandConstraints
  . checkAll $ e

compileExp :: (Name, E) -> (Set Pattern, Set Pattern)
compileExp (n, e) = generateConstraints . elab $ (n, e)

compile :: [Statement] -> String
compile ps = result
  where
    (ops, es) = partitionEithers $ map isOp ps
    isOp (Pragma p) = Left p
    isOp (Rule (Just n) e) = Right (n,e)
    isOp (Rule Nothing _) = error ""
    notBasic (pr, _) = not (pr `elem` map Pred ["move", "at"])
    sch = filter notBasic $ nub $ concatMap (schema . snd) es
    result = unlines $
      map (GD.schemaCompile ops) sch
      <> map (\e -> GD.ruleCompile e (compileExp e)) es

mkFile path p = do
  prelude <- GD.readPrelude
  writeFile path $ prelude <> p

demo name rules = do
    case find (byName) rules of
      Just (Rule _ r) -> do
        let f = (name, r)
        --let f = (name, fromJust $ lookup name rules)
        pprint $ snd f
        putStrLn "~~~~~~~~~"
        let f' = elab f
        pprint f'
        putStrLn "~~~~~~~~~"
        let (body, h) = generateConstraints' f'
        mapM_ pprint body
        putStrLn "---------"
        mapM_ pprint h
        putStrLn "~~~~~~~~~"
      _ -> error ""
  where
    byName (Rule (Just n) _) | n == name = True
    byName _ = False

main1 = do
  pr0 <- readFile "ttt.turn"
  let pr = unlines . takeWhile (/= "exit") . filter (not . (== "--") . take 2) . lines $ pr0
  let name _ r@(Rule (Just _) _) = r
      name n (Rule Nothing r) = Rule (Just n) r
      name _ x = x
  let rules = zipWith name [ "r" <> show i | i <- [1..] ] (assertParse program pr)
  -- demo "r2" rules
  let result = compile rules
  putStrLn $ "generated derp:\n" <> result
  mkFile "out.derp" $ result
  pure result

main2' input = do
  let rs = assertParse prog $ lexComments ";" input
  --print rs
  let out = D.iterRules rs
  putStrLn "\nresult:"
  mapM_ (putStrLn . spaces . map pp) $ out
  putStrLn "."

main2 = do
  input <- readFile "test.derp"
  main2' input

main3 = do
  str <- main1
  main2' str

main = main3
