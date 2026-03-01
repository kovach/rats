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
import Data.Function ((&))
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
    go (EVar (TermVar (NegVar v))) =
      if not (v `elem` vs)
         then EVar (TermVar (ExVar v))
         else EVar (TermVar (NegVar v))
    go (EVar x) = trace ("!!! " <> show x<> " : " <> show vs) $ EVar x
    go x = x

elabCVars = eTermTraverse go
  where
    go (TermChoiceVar Nothing v) = do
      v' <- fresh (pp v)
      pure (TermChoiceVar (Just $ NegVar v') v)
    go e = pure e

ifNothing = flip fromMaybe

elabNegAtoms ruleName e = eTraverse go e
  where
    go (Atom p@(Pattern AtomNeg (PVar mv Nothing) ts)) = do
      mv' <- ifNothing mv <$> (NegVar <$> freshAtomVar p);
      -- let var = if isBuiltin ts then ExVar m else NegVar m
      pure $ Atom $ Pattern AtomNeg (AllVars mv' ruleName) ts
    go (Atom (Pattern AtomNeg _ _)) = error ""
    go e' = pure e'

elabPosAtoms ruleName e = eTraverse go e
  where
    go (Atom p@(Pattern AtomPos (PVar mv Nothing) ts)) = do
      m <- ifNothing mv <$> (PosVar <$> freshAtomVar p)
      pure $ Atom $ Pattern AtomPos (PVar (Just $ m) (Just ruleName)) ts
    --go (Atom p@(Pattern AtomAsk NoVars ts)) = do
    --  m <- freshAtomVar p;
    --  pure $ Atom $ Pattern AtomAsk (AllVars (PosVar m) vs ruleName) ts
    go (Atom (Pattern AtomPos _ _)) = error ""
    go (Atom (Pattern AtomAsk _ _)) = error ""
    go e' = pure e'

--todo
--elabPosVars vs ruleName e = eTermTraverse go e
--  where
--    go (TermFreshVar v) = pure $ TermId $ Id (ruleName <> ":" <> pp v) vs
--    go e' = pure e'

elab' r e = do
  -- mark existential variables,
  -- fresh names on choice vars,
  -- introduce bound variables
  e1 <- pure e >>= elabEVars >>= elabCVars >>= elabNegAtoms r
  --let vs = negVars e1
  -- introduce fresh ids that capture the negVars for
  --   positive atoms, and
  --   `TermFreshVar` instances
  elabPosAtoms r e1
    -- >>= elabPosVars r

elab :: (Name, E) -> E
elab = evalM . uncurry elab'

type MonadPatternWriter m = MonadWriter [Constraint] m

checkTerm :: MonadPatternWriter m => Term -> m ()
checkTerm = \case
  TermChoiceVar (Just v') v ->
    tell [Val (TermVar v') (TermVar v)]
  _ -> pure ()

check :: MonadPatternWriter m => E -> m I
check (Atom p@(Pattern AtomNeg (AllVars v@(ExVar _) _) ts)) | isBuiltin ts = do
  mapM_ checkTerm ts
  tell [Constraint p]
  pure (I (leftEnd v) (rightEnd v))
check (Atom (Pattern AtomNeg (AllVars _ _) ts)) | isBuiltin ts = error ""
check (Atom p@(Pattern sign (AllVars v name) ts)) = do
  mapM_ checkTerm ts
  case sign of
    AtomPos -> do
      tell [Constraint p, (leftEnd v) `Lt` (rightEnd v)]
    AtomNeg -> do
      tell [Constraint p, (leftEnd v) `Lt` (rightEnd v)]
    AtomAsk -> do
      tell [Try p, (leftEnd v) `Lt` (rightEnd v)]
  pure (I (leftEnd v) (rightEnd v))
check (EVar t) = do
  tell [L t `Lt` R t]
  pure $ I (L t) (R t)
check (Atom p) = error $ pp p
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
check (SameIsh a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [al `Lt` bl, ar `Eql` br]
  pure $ I al ar
check (Instead a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [al `Eql` bl, ar `Eql` br]
  pure $ I al ar

checkAll :: E -> [Constraint]
checkAll = snd . runWriter . check

-- expand and simplify constrains:
expandConstraint :: Constraint -> [Constraint]
expandConstraint (Cmp op (Max a b) c) | opIneq op = expandConstraints [Cmp op a c, Cmp op b c]
expandConstraint (Cmp op a (Min b c)) | opIneq op = expandConstraints [Cmp op a b, Cmp op a c]
expandConstraint (Cmp OpEq a a') | a == a' = []
expandConstraint (Cmp OpLt _ Top) = []
expandConstraint (Cmp OpLt Top _) = trace "`Top <` error" []
expandConstraint (Cmp OpLt _ Bot) = trace "`< Bot` error" []
expandConstraint (Cmp OpLt Bot _) = []
-- expandConstraint p@(Cmp _ (Min _ _) _) = error $ pp p  -- no disjunctive comparisons
-- expandConstraint p@(Cmp _ _ (Max _ _)) = error $ pp p  -- no disjunctive comparisons
expandConstraint x = [x]

expandConstraints :: [Constraint] -> [Constraint]
expandConstraints = concatMap expandConstraint

minus a b = filter (not . (`elem` b)) a
endpoints v = [leftEnd v, rightEnd v]

quantElimConstraintsGroup local ps = quantElimConstraints' evs' pvst ps
  where
    vs = constraintsVars ps
    evst = concatMap (\v -> [leftEnd v, rightEnd v]) $ filter isExVar vs
    pvs = filter isPosVar vs
    pvst = concatMap endpoints pvs
    evs' = evst <> (concatMap endpoints $ pvs `minus` local)

quantElimConstraints :: [Constraint] -> [Constraint]
quantElimConstraints ps = quantElimConstraints' evs pvs ps
  where
    vs = constraintsVars ps
    evs = concatMap endpoints $ filter isExVar vs
    pvs = concatMap endpoints $ filter isPosVar vs

-- TODO: handle min, max in terms
quantElimConstraints' evs pvs ps = out
  where
    chk x = if c then x else error ""
    out' = nub $ rest <> elimAll <> elimEx
    out = chk out'
    c = all ok out'
    ok (Cmp _ a b) = not (a `elem` evs || b `elem` evs)
    ok _ = True
    (cmps, rest) = partition isCmp ps
    elimEx = elimVars evs cmps
    elimAll = elimVars pvs elimEx
    isGt v (Cmp OpLt _ v') = v == v'
    isGt _ _ = False
    isLt v (Cmp OpLt v' _) = v == v'
    isLt _ _ = False
    isEq v (Cmp OpEq a b) | v == a && v /= b = Just b
    isEq v (Cmp OpEq a b) | v == b && v /= a = Just a
    isEq _ _ = Nothing
    isCmp (Cmp {}) = True
    isCmp _ = False
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
        other = filter isOther cmps
        isOther (Cmp _ a b) = a /= v && b /= v
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

isPos _vs (Constraint (Pattern AtomPos _ _)) = True
isPos _vs (Constraint (Pattern{})) = False
isPos _vs (Eq _ _) = False
isPos _vs (Val _ _) = False
isPos vs (Cmp _ a b) = any (tContainsId vs) [a,b]
isPos vs (IsId t) = termContainsId vs t
isPos _vs (Try _) = True
isPos vs (Other ts) = any (termContainsId vs) ts

genMagicLt :: Rule -> Rule
genMagicLt (Rule negSet _) = result
  where
    neg = Set.toList negSet
    cmps = map termOfEndpoint $ mapMaybe (\case Cmp OpLt a _ -> Just a; _ -> Nothing) neg
    termOfEndpoint (L x) = x
    termOfEndpoint (R x) = x
    termOfEndpoint _ = error ""
    toMSPred term =
      Other [TermPred "wantLt", term]
    magicRule = Rule (Set.filter (not . isCmp) negSet) (Set.fromList $ map toMSPred cmps)
    isCmp (Cmp {}) = True
    isCmp _ = False
    result = magicRule

-- Use pvs as the set of positive variables
-- splitConstraints :: [Var] -> [Constraint] -> Rule
splitConstraints pvs x = result
  where
    (pos, neg) = partition (isPos pvs) x
    negSet = Set.fromList neg
    result = Rule negSet (Set.fromList pos)

type Constraints = Set Constraint

scm f s = Set.map f s & Set.unions

fixpoint :: Collection' t => (t -> t) -> t -> t
fixpoint f x = let x' = f x in if size x' == size x then x else fixpoint f x'

-- transitive closure
transLe :: Ord a => Set (a,a) -> Set (a,a)
transLe = fixpoint step
  where
    step lts = lts <> (Set.cartesianProduct lts lts & scm (\((x,a),(b,y)) -> if a == b then one (x,y) else none))

toLes :: Constraints -> Set (Var, Var)
toLes cs = result
  where
    result = base & transLe & scm toLL
    toLL = \case (L (TermVar u), L (TermVar v)) -> one (u,v); _ -> none
    base = scm (isLt <> isEq) cs <> vs0 <> vs1
    isLt = \case Cmp OpLt a b -> one (a,b); _ -> none
    isEq = \case Cmp OpEq a b -> ofList [(a,b), (b,a)]; _ -> none
    clist = Set.toList cs
    vs0 = Set.fromList $ do
      Constraint (Pattern AtomNeg (PVar (Just v) _) ts) <- clist
      v' <- termsVars ts
      pure (L (TermVar v), L (TermVar v'))
    vs1 = Set.fromList $ do
      Constraint (Pattern _ (PVar (Just v) _) ts) <- clist
      v' <- termsVars ts
      pure (L (TermVar v'), L (TermVar v))

ignoreCase h v = varName v `elem` (Set.map varName h)

data VarScope = VS (Set Var) (Set Var)
  deriving (Eq, Show)
instance PP VarScope where
  pp (VS h b) = bwrap $ pp h <> ":" <> pp b
mergeVS (VS h1 b1) (VS h2 b2) =
  let h = (h1 <> h2)
      b = (b1 <> b2) & Set.filter (not . ignoreCase h)
   in VS h b

depVarSets :: [Constraint] -> [VarScope]
depVarSets cs = mergeSeq 10 . map removeHead . mergeIdentical $ ans
  where
    removeHead (VS h b) = (VS h $ Set.filter (not . ignoreCase h) b)
    --removeHead (h, b) = (h, Set.filter (not . (`elem` h)) b)
    mergeIdentical [] = []
    mergeIdentical ((h,b) : xs) =
      -- take out all groups with the same dependencies
      let (same, rest) = partition ((== b) . snd) xs
       in (VS (Set.fromList $ h : map fst same) b) : mergeIdentical rest
    -- TODO cleanup
    mergeSeq 0 xs = error "gas"
    mergeSeq n xs = case mapMaybe (mergeSeq' xs) xs of
                    xs':_ -> mergeSeq (n-1) xs'
                    [] -> xs
    mergeSeq' xs v1 =
      case findPick (canMergeSeq v1) (filter (/= v1) xs) of
        Nothing -> Nothing
        Just (v2,xs') -> Just $ (mergeVS v1 v2) : xs'
    canMergeSeq t1@(VS _ b1) t2@(VS h2 b2) =
      Set.isSubsetOf b2 b1
      && (b1 `Set.difference` b2) `Set.isSubsetOf` h2
    ans = [ (v, downward v les) | v <- heads ]
    heads = mapMaybe findPos cs
    les = toLes $ Set.fromList cs
    downward v = scm (\(a,b) -> if b == v then one a else none)
    findPos (Constraint (Pattern AtomPos (PVar (Just v) _) _)) = Just v
    findPos _ = Nothing -- TODO AtomAsk?

addScopes :: Name -> [VarScope] -> [Constraint]
addScopes n = concatMap fix
  where
    fix (VS hs ds) = concatMap f hs
      where
        deps = Set.toList ds
        f v = [ Eq (TermVar v) $ TermId $ Id (n <> ":" <> pp v) deps
              , IsId (TermVar v) ]

groupScope :: VarScope -> [Constraint] -> Rule
groupScope (VS heads deps) = splitConstraints heads . map fix . sub . quantElimConstraintsGroup allVars
  where
    allVars = heads <> deps
    sub = filter (\c -> constraintVars c `subset` allVars)
    subset x y = all (`elem` y) x
    fix (Constraint (Pattern AtomPos (AllVars v n) ts)) | v `elem` deps =
      Constraint (Pattern AtomNeg (AllVars v n) ts)
    fix x = x

groupScopes :: [VarScope] -> [Constraint] -> [Rule]
groupScopes vs cs = map (\v -> groupScope v cs) vs

-- fixScopes :: [Constraint] -> [Rule]
fixScopes n c = groupScopes deps $ addScopes n deps <> c <> newLts
  where
    deps = depVarSets c
    newLts = do
      VS hs bs <- deps
      b <- TermVar <$> Set.toList hs
      a <- TermVar <$> (Set.toList bs `intersect` evs)
      pure $ Cmp OpLt (L a) (L b)

    evs = episodeVars c
    episodeVars = mapMaybe f
      where
        f (Constraint (Pattern _ (PVar (Just v) _) _)) = Just v
        f _ = Nothing

generateConstraints n e = trace (unlines $ map pp sets) c'
  where
    c' = fixScopes n c
    c = expandConstraints
        . quantElimConstraints
        . expandConstraints
        . checkAll $ e

    sets = depVarSets c

ppt f cs = trace ("!!: " <> unlines (map pp cs)) $ f cs
generateConstraints' e = splitConstraints (posVars e)
  . (ppt expandConstraints)
  . (ppt $ quantElimConstraints)
  . expandConstraints
  . checkAll $ e

-- Remove `L a < R a` checks from rule bodies.
simplRule :: Rule -> Rule
simplRule (Rule {body, head}) = Rule {body = body', head = head'}
  where
    body' = Set.filter ok body
    head' = head
    ok (Cmp OpLt (L a) (R b)) | a == b = False
    ok _ = True

compileExp :: (Name, E) -> [Rule]
compileExp pr@(n, _) = rs -- <> tryPatterns
  where
    rs = map simplRule . generateConstraints n . elab $ pr
    --r@(Rule _ h) = generateConstraints . elab $ pr
    --tryPatterns = mapMaybe fixTry $ Set.toList h
    --fixTry (Try p) = error ""
      --Just $ Rule b' h'
      --where
      --  p' = freshPattern p
      --  b' = Set.fromList $ [Try p', NegChose x]
      --  h' = Set.fromList $ [Constraint p']
    --fixTry _ = Nothing
    --x = NegVar "X"
    -- freshPattern (Pattern sign (AllVars _ ds n) (p : vs)) =
    --   Pattern sign (AllVars x ds n) ts'
    --     where
    --       ts' = p : (map (\i -> TermVar $ NegVar $ "X" <> show i) [1.. length vs])
    -- freshPattern _ = error ""

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
  let outFile = (base ++ ".derp")
  writeFile outFile result
  putStrLn $ "wrote file " <> outFile
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

-- TODO
-- error handling
-- debug/info log
