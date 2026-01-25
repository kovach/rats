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

import Types
import Parser
import ParserCombinator
import MMap (MMap)

-- todo
-- type MonadComp m = (MonadPatternWriter m, MonadFreshVarState m)
-- type MC a = WriterT [Pattern] (State (MMap String (Sum Int))) a

-- todo: one case
pattern PP p ts <- Pattern _ _ (TermPred p : ts)
pattern PPI p i ts <- Pattern _ (PVar2 i _ _) (TermPred p : ts)

leftEnd t = L (TermVar t)
rightEnd t = R (TermVar t)

predString (Pred s) = s
predPattern :: Pattern -> Maybe Pred
predPattern (PP p _) = Just p
predPattern _ = Nothing
patternVars (Pattern _ PVar0 ts) = varTerms ts
patternVars (Pattern _ (PVar2 i _ _) ts) = i : varTerms ts
patternVars (Cmp _ a b) = tVars a <> tVars b
patternVars (IsId t) = termVars t
varTerms = concatMap termVars
termVars (TermVar (Var v)) = [Var v]
termVars (TermId (Id _ vs)) = vs
termVars (TermPred {}) = []
termVars (TermFreshVar {}) = []
termVars (TermExt _) = []
termVars TermBlank = []
tVars (L t) = termVars t
tVars (R t) = termVars t
tVars (Min a b) = tVars a <> tVars b
tVars (Max a b) = tVars a <> tVars b
tVars Top = []

pattern Lt a b = Cmp OpLt a b
pattern Le a b = Cmp OpLe a b
pattern Eql a b = Cmp OpEq a b

eTraverse' :: Applicative m => (E -> m ()) -> E -> m ()
eTraverse' f e0 = eTraverse (\e -> f e *> pure e) e0 *> pure ()

eTraverse :: Applicative m => (E -> m E) -> E -> m E
eTraverse f = go
  where
    go e@(Atom _) = f e
    go (After e) = After <$> go e
    go (And a b) = And <$> (go a) <*> (go b)
    go (Seq a b) = Seq <$> (go a) <*> (go b)
    go (Par a b) = Par <$> (go a) <*> (go b)
    go (Over a b) = Over <$> (go a) <*> (go b)
    go (Same a b) = Same <$> (go a) <*> (go b)

eTermTraverse :: forall m. Applicative m => (Term -> m Term) -> E -> m E
eTermTraverse f = eTraverse go
  where
    go :: E -> m E
    go (Atom (Pattern ty mv ts)) =
      (\ts' -> Atom (Pattern ty mv ts')) <$>
        (sequenceA $ map (termTraverse f) ts)
    go e = pure e

termTraverse :: Applicative m => (Term -> m Term) -> Term -> m Term
termTraverse f = go
  where
    go t = f t

tTraverse:: Applicative m => (T -> m T) -> T -> m T
tTraverse f =  go
  where
    go t@(L _) = f t
    go t@(R _) = f t
    go Top = f Top
    go (Min a b) = Min <$> go a <*> go b
    go (Max a b) = Max <$> go a <*> go b


freshAtomVar p | Just pr <- predPattern p = fresh $ capitalize $ predString pr
freshAtomVar _ = fresh "_id"

idConstructor ruleName p vs = do
  m <- freshAtomVar p
  pure $ Id (ruleName <> ":__" <> m) vs

vars :: E -> [Var]
vars = nub . execWriter . eTraverse' go
  where
    go (Atom p) = tell (patternVars p)
    go _ = pure ()

posVars :: E -> [Var]
posVars = nub . execWriter . eTraverse' go
  where
    go (Atom (Pattern AtomPos (PVar2 v _ _) _)) = tell [v]
    go _ = pure ()

schema :: E -> [(Pred, Int)]
schema = execWriter . eTraverse go
  where
    go e@(Atom (PP pr ts)) = do tell [(pr, length ts)]; pure e
    go e = pure e


elabNegAtoms ruleName e = eTraverse go e
  where
    vs = vars e
    go (Atom p@(Pattern AtomNeg PVar0 ts)) = do
      m <- freshAtomVar p;
      pure $ Atom $ Pattern AtomNeg (PVar2 (Var m) vs ruleName) ts
    go e' = pure e'

elabPosAtoms vs ruleName e = eTraverse go e
  where
    go (Atom p@(Pattern AtomPos PVar0 ts)) = do
      m <- freshAtomVar p;
      pure $ Atom $ Pattern AtomPos (PVar2 (Var m) vs ruleName) ts
    go e' = pure e'

elabPosVar vs ruleName e = eTermTraverse go e
  where
    go (TermFreshVar v) = pure $
      TermId $ Id (ruleName <> ":" <> v) vs
    go e' = pure e'

type Rule = (Name, E)

elabNegPos r e0 = do
  e1 <- elabNegAtoms r e0
  let vs = vars e1
  elabPosAtoms (vars e1) r e1 >>= elabPosVar vs r
elab = evalM . uncurry elabNegPos

elabAll :: [Rule] -> [E]
elabAll = evalM . mapM (uncurry elabNegPos)

type MonadPatternWriter m = MonadWriter [Pattern] m

check :: MonadPatternWriter m => E -> m I
check (Atom p@(Pattern AtomPos (PVar2 v vs name) _)) = do
  let i = Id (name <> ":__" <> pp v) vs
  tell [p, (leftEnd v) `Lt` (rightEnd v), Eq (TermVar v) (TermId i)];
  pure (I (leftEnd v) (rightEnd v))
check (Atom p@(Pattern AtomNeg (PVar2 v _ _) _)) = do
  tell [p, (leftEnd v) `Lt` (rightEnd v)];
  pure (I (leftEnd v) (rightEnd v))
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
check (Seq a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [ar `Le` bl]
  pure $ I al br
check (Over a b) = do
  I al ar <- check a
  I bl br <- check b
  tell [al `Lt` bl, br `Lt` ar]
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
expandConstraint (Cmp _ _ Top) = []
expandConstraint p@(Cmp _ (Min _ _) _) = error $ pp p  -- no disjunctive comparisons
expandConstraint p@(Cmp _ _ (Max _ _)) = error $ pp p  -- no disjunctive comparisons
expandConstraint x = [x]

expandConstraints :: [Pattern] -> [Pattern]
expandConstraints = concatMap expandConstraint

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
isPos vs (Cmp _ a b) = any (tContainsId vs) [a,b]
isPos vs (IsId t) = termContainsId vs t

splitConstraints :: [Var] -> [Pattern] -> (Set Pattern, Set Pattern)
splitConstraints pvs x =
  let (pos, neg) = partition (isPos pvs) x
   in (Set.fromList neg, Set.fromList pos)

generateConstraints e = splitConstraints (posVars e) $ expandConstraints . checkAll $ e

compileExp e = result
  where
    e' = elab e
    result = ruleCompile . generateConstraints $ e'

compile :: [(Name, Statement)] -> String
compile ps = result
  where
    (ops, es) = partitionEithers $ map isOp ps
    isOp (_, Pragma p) = Left p
    isOp (n, Rule e) = Right (n,e)
    sch = nub $ concatMap (schema . snd) es
    result = unlines $
      map (schemaCompile ops) sch
      <> map compileExp es

commas = intercalate ", "
args = pwrap . intercalate ", "

ruleCompile :: (Set Pattern, Set Pattern) -> String
ruleCompile (body, h) =
  if Set.size body == 0 then
   unwords (map patternCompile1 $ Set.toList h)
  else
    commas (map patternCompile $ Set.toList h)
    <> "\n  :-\n"
    <> commas (map patternCompile $ Set.toList body)
    <> "\n."

schemaCompile :: [Pred] -> (Pred, Int) -> String
schemaCompile countPreds (p, arity) =
  ".decl " <> pp p <> args (map (\i -> "x" <> show i <> ":Term") [1..(arity+1)])
  <> (if p `elem` countPreds then "" else " .output " <> pp p)

patternCompile1 = (<> ".") . patternCompile
patternCompile :: Pattern -> String
patternCompile = \case
  PPI p i ts -> pp p <> args (pp i : map termCompile ts)
  Pattern {} -> error ""
  Cmp op a b -> opString op <> pwrap (commas $ map tCompile [a,b])
  Eq a b -> termCompile a <> " = " <> termCompile b
  IsId t -> "IsId" <> pwrap (termCompile t)
opString OpLt = "Lt"
opString OpLe = "Le"
opString OpEq = "Eq"
termCompile :: Term -> String
termCompile = \case
  TermVar v -> pp v
  TermPred pr -> cons "TermPred" [show $ pp pr]
  TermId i -> cons "TermId" [compileId i]
  TermFreshVar _ -> error ""
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

mkFile path p = do
  prelude <- readFile "prelude.dl"
  writeFile path $ prelude <> p

exp = assertParse expr
exp' = assertParse (expr <* ws <* char '.')

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
  , ("foo", exp ">d, !e !E")
  ]

demo name rules = do
  case lookup name rules of
    Just (Rule r) -> do
      let f = (name, r)
      --let f = (name, fromJust $ lookup name rules)
      pprint $ snd f
      putStrLn "~~~~~~~~~"
      let [f'] = elabAll [f]
      pprint f'
      putStrLn "~~~~~~~~~"
      let (body, h) = generateConstraints f'
      mapM_ pprint body
      putStrLn "---------"
      mapM_ pprint h
      putStrLn "~~~~~~~~~"
    _ -> error ""

main = do
  pr0 <- readFile "card.tin"
  let pr = unlines . takeWhile (/= "exit") . lines $ pr0
  let rules = zip [ "r" <> show i | i <- [1..] ] (assertParse program pr)
  demo "r5" rules
  let result = compile rules
  mkFile "out.dl" $ result
