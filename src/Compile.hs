{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
--module Compile (main1, main1', main2, main3, parseOne) where
module Compile  where

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
import System.Directory (createDirectoryIfMissing)
import Data.Char
import Data.List.Split

import Basic
import Types
import qualified Parser as TP
import ParserCombinator (assertParse, lexComments)
import MMap (MMap)
import qualified MMap as M
import qualified Derp.Core as D
import qualified Derp.Parse as DP
import qualified Derp.Gen as GD
--import CatShelf hiding (parse, Term, Pred, Var)
--import qualified CatShelf as CS
import qualified ConcatParse as P

data VarScope = VS (Set Var) (Set Var)
  deriving (Eq, Show)
instance PP VarScope where
  pp (VS h b) = bwrap $ pp h <> ":" <> pp b
ignoreCase h v = varName v `elem` (Set.map varName h)
mergeVS (VS h1 b1) (VS h2 b2) =
  let h = (h1 <> h2)
      b = (b1 <> b2) & Set.filter (not . ignoreCase h)
   in VS h b

leftEnd t = L (TermVar t)
rightEnd t = R (TermVar t)

predPattern :: Pattern -> Maybe Pred
predPattern (PP p _) = Just p
predPattern _ = Nothing

freshAtomVar p | Just (Pred ('#':pr)) <- predPattern p = fresh $ capitalize pr
freshAtomVar p | Just (Pred pr) <- predPattern p = fresh $ capitalize pr
freshAtomVar _ = fresh "_id"

-- todo: freeVars only
-- vars :: E -> [Var]
-- vars = nub . execWriter . eTraverse' go
--   where
--     go (Atom p) = tell (patternVars p)
--     go (EVar t) = tell (termVars t)
--     go _ = pure ()
--
-- freeVars :: E -> [Var]
-- freeVars = filter isFreeVar . vars
-- posVars :: E -> [Var]
-- posVars = filter isPosVar . vars

patternBoundVars :: E -> [Var]
patternBoundVars = filter isFreeVar . nub . execWriter . eTraverse' go
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
    go (EVar (TermVar (FreeVar v))) =
      if not (v `elem` vs)
         then EVar (TermVar (ExVar v))
         else EVar (TermVar (FreeVar v))
    go (EVar x) = trace ("!!! " <> show x<> " : " <> show vs) $ EVar x
    go x = x

elabCVars = eTermTraverse go
  where
    go (TermChoiceVar Nothing v) = do
      v' <- fresh (pp v)
      pure (TermChoiceVar (Just $ FreeVar v') v)
    go e = pure e

ifNothing = flip fromMaybe

elabFreeAtoms ruleName e = eTraverse go e
  where
    go (Atom p@(Pattern AtomFree (PVar mv Nothing) ts)) = do
      mv' <- ifNothing mv <$> (FreeVar <$> freshAtomVar p);
      -- let var = if isBuiltin ts then ExVar m else FreeVar m
      pure $ Atom $ Pattern AtomFree (AllVars mv' ruleName) ts
    go (Atom p@(Pattern AtomNeg (PVar mv Nothing) ts)) = do
      mv' <- ifNothing mv <$> (FreeVar <$> freshAtomVar p);
      pure $ Atom $ Pattern AtomNeg (AllVars mv' ruleName) ts
    go (Atom (Pattern AtomFree _ _)) = error ""
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

exceptionPredicates :: E -> [(Pred, E)]
exceptionPredicates = nub . execWriter . eTraverse' go
  where
    go (Instead (PP l _) r) = tell [(l,r)]
    go _ = pure ()

elab' (TRule r e) = do
  -- mark existential variables,
  -- fresh names on choice vars,
  -- introduce bound variables
  e1 <- pure e >>= elabEVars >>= elabCVars >>= elabFreeAtoms r
  --let vs = negVars e1
  -- introduce fresh ids that capture the negVars for
  --   positive atoms, and
  --   `TermFreshVar` instances
  e2 <- elabPosAtoms r e1
  pure $ TRule r e2
    -- >>= elabPosVars r

elab :: TRule -> TRule
elab = evalM . elab'

type MonadPatternWriter m = MonadWriter [Constraint] m

checkTerm :: MonadPatternWriter m => Term -> m ()
checkTerm = \case
  TermChoiceVar (Just v') v ->
    tell [Val (TermVar v') (TermVar v)]
  _ -> pure ()

checkCmp cmp a b =
  case cmp of
    ECEq -> [a `Eql` b]; ECNone -> []
    ECLt -> [a `Lt` b]; ECGt -> [b `Lt` a]

check :: MonadPatternWriter m => E -> m I
check (Atom p@(Pattern AtomFree (AllVars v@(ExVar _) _) ts)) | isBuiltin ts = do
  mapM_ checkTerm ts
  tell [Constraint p]
  pure (I (leftEnd v) (rightEnd v))
check (Atom (Pattern AtomFree (AllVars _ _) ts)) | isBuiltin ts = error ""
check (Atom p@(Pattern sign (AllVars v _name) ts)) = do
  mapM_ checkTerm ts
  case sign of
    AtomPos  -> tell [Constraint p, (leftEnd v) `Lt` (rightEnd v)]
    AtomFree -> tell [Constraint p, (leftEnd v) `Lt` (rightEnd v)]
    AtomAsk  -> tell [Try p, (leftEnd v) `Lt` (rightEnd v)]
    AtomNeg  -> tell [Constraint p]
  pure (I (leftEnd v) (rightEnd v))
check (Atom p) = error $ pp p
check (SameNot a p@(Pattern _ (AllVars v _) _)) = do
  I al ar <- check a
  let (bl, br) = (leftEnd v, rightEnd v)
  tell [Not [Constraint p, al `Eql` bl, br `Eql` ar]]
  pure $ I al ar
check e@(SameNot {}) = error $ pp e
check (EVar t) = do
  tell [L t `Lt` R t]
  pure $ I (L t) (R t)
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
check (Instead{}) = error "unreachable. Instead is pre-processed."
check (GenAnd l r a b) = do
  I al ar <- check a
  I bl br <- check b
  tell $ [Max al bl `Lt` Min ar br] <> checkCmp l al bl <> checkCmp r ar br
  pure $ I (max' l al bl) (min' r ar br)

max' ECEq a _ = a
max' ECLt _ b = b
max' ECGt a _ = a
max' _ a b = Max a b
min' ECEq a _ = a
min' ECLt a _ = a
min' ECGt _ b = b
min' _ a b = Min a b


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
    (cmps1, rest) = partition isCmp ps
    elimEx = elimVars evs cmps1
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
isPos _vs (Constraint _) = False
isPos _vs (Eq _ _) = False
isPos _vs (Val _ _) = False
isPos vs (Cmp _ a b) = any (tContainsId vs) [a,b]
isPos vs (IsId t) = termContainsId vs t
isPos _vs (Try _) = True
isPos vs (Other ts) = any (termContainsId vs) ts
isPos _vs (Not _) = False

-- genMagicLt :: Rule -> Rule
-- genMagicLt (Rule negSet _) = result
--   where
--     neg = Set.toList negSet
--     cmps = map termOfEndpoint $ mapMaybe (\case Cmp OpLt a _ -> Just a; _ -> Nothing) neg
--     termOfEndpoint (L x) = x
--     termOfEndpoint (R x) = x
--     termOfEndpoint _ = error ""
--     toMSPred term =
--       Other [TermPred "wantLt", term]
--     magicRule = Rule (Set.filter (not . isCmp) negSet) (Set.fromList $ map toMSPred cmps)
--     isCmp (Cmp {}) = True
--     isCmp _ = False
--     result = magicRule

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

prs :: Show a => Set (a, a) -> String
prs = unlines . map show . Set.toList
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
      Constraint (Pattern AtomFree (PVar (Just v) _) ts) <- clist
      v' <- termsVars ts
      pure (L (TermVar v), L (TermVar v'))
    vs1 = Set.fromList $ do
      Constraint (Pattern _ (PVar (Just v) _) ts) <- clist
      v' <- termsVars ts
      pure (L (TermVar v'), L (TermVar v))

depVarSets :: [Constraint] -> [VarScope]
depVarSets cs = mergeSeq . map removeHead . mergeIdentical $ ans
  where
    ans = [ (v, downward v les) | v <- heads ]
    heads = mapMaybe findPos cs
    les = toLes $ Set.fromList cs
    downward v = Set.map fst . Set.filter ((== v) . snd)
    findPos (Constraint (Pattern AtomPos (PVar (Just v) _) _)) = Just v
    findPos _ = Nothing -- TODO AtomAsk?

    mergeIdentical [] = []
    mergeIdentical ((h,b) : xs) =
      -- take out all groups with the same dependencies
      let (same, rest) = partition ((== b) . snd) xs
       in (VS (Set.fromList $ h : map fst same) b) : mergeIdentical rest
    removeHead (VS h b) = (VS h $ Set.filter (not . ignoreCase h) b)
    -- TODO cleanup
    mergeSeq xs = case mapMaybe (uncurry mergeSeq') $ picks xs of
                    xs':_ -> mergeSeq xs'
                    [] -> xs
    mergeSeq' v1 xs = do
      (v2, xs') <- findPick (canMergeSeq v1) xs
      pure $ (mergeVS v1 v2) : xs'
    -- Scopes can be safely merged into one
    canMergeSeq (VS _ b1) (VS h2 b2) =
      Set.isSubsetOf b2 b1
      && (b1 `Set.difference` b2) `Set.isSubsetOf` h2

addScopes :: Name -> [VarScope] -> [Constraint]
addScopes n = concatMap fix
  where
    fix (VS hs ds) = concatMap f hs
      where
        deps = Set.toList ds
        f v = [ Eq (TermVar v) $ TermId $ Id (n <> ":" <> pp v) deps
              , IsId (TermVar v) ]

groupScope :: VarScope -> [Constraint] -> Rule
groupScope (VS heads deps) = splitConstraints heads . expandConstraints . map fix . sub . quantElimConstraintsGroup allVars
  where
    allVars = heads <> deps
    sub = filter (\c -> constraintVars c `subset` allVars)
    subset x y = all (`elem` y) x
    fix (Constraint (Pattern AtomPos (AllVars v n) ts)) | v `elem` deps =
      Constraint (Pattern AtomFree (AllVars v n) ts)
    fix x = x

groupScopes :: [VarScope] -> [Constraint] -> [Rule]
groupScopes vs cs = map (\v -> groupScope v cs) vs

fixScopes :: Name -> [Constraint] -> [Rule]
fixScopes n c = groupScopes deps $ addScopes n deps <> c -- <> newLts -- TODO: breaks ~
  where
    deps = depVarSets c
    --newLts = do
    --  VS hs bs <- deps
    --  b <- TermVar <$> Set.toList hs
    --  a <- TermVar <$> (Set.toList bs `intersect` evs)
    --  pure $ Cmp OpLt (L a) (L b)
    --evs = episodeVars c
    --episodeVars = mapMaybe f
    --  where
    --    f (Constraint (Pattern _ (PVar (Just v) _) _)) = Just v
    --    f _ = Nothing

generateConstraints (TRule n e) = trace ("f: " <> (unlines $ map pp sets)) c'
  where
    c' = fixScopes n c
    c = expandConstraints
        . quantElimConstraints
        . expandConstraints
        . checkAll $ e

    sets = depVarSets c

-- ppt f cs = trace ("!!: " <> unlines (map pp cs)) $ f cs
-- generateConstraints' e = splitConstraints (posVars e)
--   . (ppt expandConstraints)
--   . (ppt $ quantElimConstraints)
--   . expandConstraints
--   . checkAll $ e

rewritePredicate from to = eMap fix
  where
    fix (Atom (PPP p a b c)) | from == p = Atom $ PPP to a b c
    fix x = x

-- note: exception condition cannot depend on
rewriteOneException name' p = eMap fix
  where
    -- should handle several by matching on LHS/(name', p) pairs
    fix (Instead (PPP _ a b c) _) = Same (Atom (PPP name' a b c)) (Atom (PPP p AtomPos noPVar [{-TODO-}]))
    fix x = x

-- An exception rewrites a *target* conditionally
-- implemented by three rules:
--   - property asserts the condition
--   - default generates the target when condition fails to hold
--   - exception generates the alternate when condition does hold
-- Applied before all other passes, so allowed to generate unelaborated Turn rules.
handleExceptions :: [TRule] -> [TRule]
handleExceptions trs = result
  where
    result = reverse $ foldl' step acc trs
    acc = []
    shift n (Pred name) = Pred $ name <> "/" <> n
    targets = exceptionPredicates
    step es tr@(TRule n e) =
        case targets e of
          [] -> tr:es
          [(x,rhs)] -> newRules x rhs tr <> map (trMap $ rewritePredicate x (shift n x)) es
          _ -> error "todo"
    newRules p rhs (TRule n e) = [ property, default_, exception ]
      where
        p' = shift n p
        checkName = Pred $ "exn/" <> n
        property = TRule (n <> "/prop") $ rewriteOneException p' checkName e
        default_ = TRule (n <> "/default") $ sames $
          [ Atom (PPP p' AtomFree NoVars [])  -- todo handle parameters to target
          , (Atom (PPP checkName AtomNeg NoVars [])) -- todo handle parameters to prop
          , Atom (PPP p AtomPos NoVars []) ]
        exception = TRule (n <> "/exception") $ sames $
          [ Atom (PPP p' AtomFree NoVars [])
          , (Atom (PPP checkName AtomFree NoVars []))
          , rhs ]
        sames = foldl1' Same

-- Remove `L a < R a` checks from rule bodies.
simplRule :: Rule -> Rule
simplRule (Rule {body, head = h}) = Rule {body = body', head = head'}
  where
    body' = Set.filter ok body
    head' = h
    ok (Cmp OpLt (L a) (R b)) | a == b = False
    ok _ = True

compileExp :: TRule -> [Rule]
compileExp pr@(TRule _n _) = rs -- <> tryPatterns
  where
    rs = map simplRule . generateConstraints . elab $ pr
    --r@(Rule _ h) = generateConstraints . elab $ pr
    --tryPatterns = mapMaybe fixTry $ Set.toList h
    --fixTry (Try p) = error ""
      --Just $ Rule b' h'
      --where
      --  p' = freshPattern p
      --  b' = Set.fromList $ [Try p', NegChose x]
      --  h' = Set.fromList $ [Constraint p']
    --fixTry _ = Nothing
    --x = FreeVar "X"
    -- freshPattern (Pattern sign (AllVars _ ds n) (p : vs)) =
    --   Pattern sign (AllVars x ds n) ts'
    --     where
    --       ts' = p : (map (\i -> TermVar $ FreeVar $ "X" <> show i) [1.. length vs])
    -- freshPattern _ = error ""

data CompilationRec = CompilationRec
  { crResult :: String
  , crElab :: String
  }

compile :: [Statement] -> CompilationRec
compile ps = CompilationRec { crResult = result, crElab = elaborated }
  where
    (ops, es) = partitionEithers $ map isOp ps

    -- todo: not in use
    isOp (Pragma p) = Left p
    isOp (RuleStatement (Just n) e) = Right $ TRule n e
    isOp (RuleStatement Nothing _) = error ""
    notBasic (pr, _) = not (pr `elem` map Pred ["move", "at"])
    sch = filter notBasic $ nub $ concatMap (schema . trE) es

    excepted = handleExceptions es
    elaborated = unlines $ map pp $ map elab $ excepted
    result = unlines $
      map (GD.schemaCompile ops) sch
      <> map (\e -> GD.ruleBlockCompile e (compileExp e)) excepted

mkFile path p = do
  prelude <- GD.readPrelude
  writeFile path $ prelude <> p

-- demo name rules = do
--     case find (byName) rules of
--       Just (RuleStatement _ r) -> do
--         let f = TRule name r
--         --let f = (name, fromJust $ lookup name rules)
--         pprint $ r
--         putStrLn "~~~~~~~~~"
--         let f' = elab f
--         pprint f'
--         putStrLn "~~~~~~~~~"
--         let Rule body h = generateConstraints' $ trE f' -- todo
--         mapM_ pprint body
--         putStrLn "---------"
--         mapM_ pprint h
--         putStrLn "~~~~~~~~~"
--       _ -> error ""
--   where
--     byName (RuleStatement (Just n) _) | n == name = True
--     byName _ = False

genDerp ttt = do
  let name _ r@(RuleStatement (Just _) _) = r
      name n (RuleStatement Nothing r) = RuleStatement (Just n) r
      name _ x = x
  let rules = zipWith name [ "r" <> show i | i <- [1..] ] ttt
  let CompilationRec {crResult, crElab} = compile rules
  prelude <- GD.readPrelude
  pure (prelude <> crResult, crElab, crResult)

writeGenDerp base stmts = do
  (result, elabText, ruleText) <- genDerp stmts
  putStrLn $ "generated derp:\n" <> ruleText
  let outFile = base <> ".gen.derp"
  writeFile outFile result
  writeFile (base ++ ".elab.turn") elabText
  putStrLn $ "wrote file " <> outFile
  pure result


main1 :: String -> IO String
main1 base = do
  pr0 <- readFile (base ++ ".turn")
  let ttt = TP.parse pr0
  writeGenDerp base ttt

main1' base = do
  pr0 <- readFile (base ++ ".turn")
  let ttt = parseOne pr0
  _ <- writeGenDerp base ttt
  pure ()

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
  input <- readFile "layout.derp"
  main2' input

main3 = do
  str <- main1 "ttt"
  main2' str

-- Parsing Stuff --
-- TODO move this
specialTokens :: [String]
specialTokens = [ "." , "," , ":" , "~" , "&" ]
endpointMarkers :: [(Char, EndpointCmp)]
endpointMarkers = zip "~=<>" [ECNone, ECEq, ECLt, ECGt]
isEndpointJoin a b = do
  av <- lookup a endpointMarkers
  bv <- lookup b endpointMarkers
  pure (av, bv)

predArity :: P.Pred -> Int
predArity s = (+1) . length . filter (== '/') $ s

data BinOps = Over'
  deriving (Show, Eq)
turnWord = \case
    (P.Token "&") -> Just $ P.Atom "&" 3 [] []
    (P.Token ":") -> Just $ P.Term Over'
    (P.Token t) | predStart t ->
      let (_, core) = splitPrefix t
       in if core `elem` binaryTokens
          then Just $ P.Atom t 2 [] []
          else Just $ P.Atom t (predArity core) [] []
    _ -> Nothing
  where
    splitPrefix ('!':s) = ("!", s)
    splitPrefix s = ("", s)
    binaryTokens = ["is", "at", "move", "the"]
    predStart (x:_) = isLower x || x `elem` ['/', '!']
    predStart _ = False

type Mark = BinOps
instance PP BinOps where
  pp Over' = ":"
convert :: P.Word Mark -> E
convert = \case
  P.Atom p 0 l r ->
    let ts = reverse l <> r
     in case p of
          '!' : p' -> Atom (Pattern AtomPos NoVars (TermPred (Pred p') : (map convertTerm ts)))
          p'       -> Atom (Pattern AtomFree NoVars (TermPred (Pred p') : (map convertTerm ts)))
  P.Atom {} -> error "incomplete atom"
  P.BinOp0 x Over' y -> Over (convert x) (convert y)
  P.Pair l r -> And (convert l) (convert r)
  P.Nil -> error""
  P.Var _v -> error""
  P.Skip -> error""
  P.Term _t -> error""

convertTerm :: P.Word Mark -> Term
convertTerm = \case
  P.Var (P.IVar v) -> TermVar (FreeVar ("_" <> v))
  P.Var (P.GenVar v) -> TermVar (FreeVar v)
  P.Term _t -> error"todo"
  P.Atom _ 0 _ _ -> error""
  P.Atom {} -> error""
  P.Nil -> error""
  P.Skip -> error""
  P.Pair _ _ -> error""

parseOne :: String -> [Statement]
parseOne s = result
  where
    result = map (RuleStatement Nothing . convert . P.mergePred "&") x
    x = tfx s

tfx :: String -> [P.Word BinOps]
tfx = P.fx specialTokens turnWord

tfx' = map (P.mergePred "&") . P.fx specialTokens turnWord
