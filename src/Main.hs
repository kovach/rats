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

-- todo: one case
pattern PI p i ts = IdPattern i (TermPred p : ts)
pattern P ty p ts = Pattern ty (TermPred p : ts)

leftEnd (TermAfter t) = rightEnd t
leftEnd t = L t
rightEnd (TermAfter _) = Top
rightEnd t = R t

predString (Pred s) = s
predPattern :: Pattern -> Maybe Pred
predPattern (Pattern _ (TermPred p : _)) = Just p
predPattern _ = Nothing
patternVars (Pattern _ ts) = varTerms ts
patternVars (IdPattern i ts) = varTerms (i:ts)
patternVars (Cmp _ a b) = tVars a <> tVars b
patternVars (IsId t) = termVars t
varTerms = concatMap termVars
termVars (TermVar (Var v)) = [Var v]
termVars (TermVar (CVar v)) = [CVar v]
termVars (TermVar _) = []
termVars (TermId (Id _ vs)) = vs
termVars (TermPred {}) = []
termVars (TermAfter {}) = []
termVars (TermFreshVar {}) = []
termVars (TermExt _) = []
tVars (L t) = termVars t
tVars (R t) = termVars t
tVars (Min a b) = tVars a <> tVars b
tVars (Max a b) = tVars a <> tVars b
tVars Top = []

pattern Lt a b = Cmp OpLt a b
pattern Le a b = Cmp OpLe a b
pattern Eql a b = Cmp OpEq a b
pattern IdAtom i ts = Atom (IdPattern i ts)

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
    go (Atom (Pattern ty ts)) =
      (\ts' -> Atom (Pattern ty ts')) <$>
        (sequenceA $ map (termTraverse f) ts)
    go (Atom (IdPattern i ts)) =
      (\ts' -> Atom (IdPattern i ts')) <$>
        (sequenceA $ map (termTraverse f) ts)
    go e = pure e

termTraverse :: Applicative m => (Term -> m Term) -> Term -> m Term
termTraverse f = go
  where
    go (TermAfter t) = TermAfter <$> go t
    go t = f t

negUnary x = Atom (Pattern AtomDuring [TermPred (Pred x)])
posUnary x = Atom (Pattern AtomPos [TermPred (Pred x)])

freshAtomVar p | Just pr <- predPattern p = fresh $ capitalize $ predString pr
freshAtomVar _ = fresh "_id"

idConstructor ruleName p vs = do
  m <- freshAtomVar p
  pure $ Id (ruleName <> ":__" <> m) vs

vars :: E -> [Var]
vars = execWriter . eTraverse go
  where
    go (Atom p) = do tell (patternVars p); pure (Atom p)
    go e = pure e

schema :: E -> [(Pred, Int)]
schema = execWriter . eTraverse go
  where
    go e@(Atom (P _ pr ts)) = do tell [(pr, length ts)]; pure e
    go e@(Atom (PI pr _ ts)) = do tell [(pr, length ts)]; pure e
    go e = pure e


elabNeg = eTraverse go
  where
    go (Atom p@(Pattern AtomDuring ts)) = do
      m <- freshAtomVar p; pure $ IdAtom (TermVar (Var m)) ts
    go (Atom p@(Pattern AtomAfter ts)) = do
      m <- freshAtomVar p; pure $ IdAtom (TermAfter $ TermVar (Var m)) ts
    go e = pure e

elabPos ruleName e = eTraverse go e
  where
    vs = vars e
    go (Atom p@(Pattern AtomPos ts)) = do
      i <- idConstructor ruleName p vs
      pure (IdAtom (TermId i) ts)
    go e' = pure e'

elabPosVar ruleName e = eTermTraverse go e
  where
    vs = vars e
    go (TermFreshVar v) = pure $
      TermId $ Id (ruleName <> ":" <> v) vs
    go e' = pure e'

type Rule = (Name, E)

elabNegPos r = elabNeg >=> elabPos r >=> elabPosVar r
elab = evalM . uncurry elabNegPos

elabAll :: [Rule] -> [E]
elabAll = evalM . mapM (uncurry elabNegPos)

type MonadPatternWriter m = MonadWriter [Pattern] m

check :: MonadPatternWriter m => E -> m I
check (Atom p@(IdPattern i _)) = do
  tell [p, Lt (leftEnd i) (rightEnd i)];
  pure (I (leftEnd i) (rightEnd i))
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

compile :: [(Name, E)] -> String
compile ps =
  let sch = nub $ concatMap (schema . snd) ps
  in
    unlines $
      map schemaCompile sch
      <> map (ruleCompile . chk . elab) ps

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

schemaCompile (p, arity) =
  ".decl " <> pp p <> args (map (\i -> "x" <> show i <> ":Term") [1..(arity+1)])
  <> " .output " <> pp p

patternCompile1 = (<> ".") . patternCompile
patternCompile :: Pattern -> String
patternCompile = \case
  PI p i ts -> pp p <> args (map termCompile $ i : ts)
  IdPattern _ _ -> error ""
  Cmp op a b -> opString op <> pwrap (commas $ map tCompile [a,b])
  IsId t -> "IsId" <> pwrap (termCompile t)
  Pattern {} -> error ""
opString OpLt = "Lt"
opString OpLe = "Le"
opString OpEq = "Eq"
termCompile :: Term -> String
termCompile = \case
  TermVar v -> pp v -- !
  TermPred pr -> cons "TermPred" [pp pr]
  TermId i -> cons "TermId" [compileId i]
  TermAfter t -> termCompile t
  TermFreshVar _ -> error ""
  TermExt "$" -> cons "TermNum" ["autoinc()"]
  TermExt _ -> error "unhandled"
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
  pr <- readFile "card.tin"
  let rules = zip [ "r" <> show i | i <- [1..] ] (assertParse program pr)
  demo "r3" rules
  let result = compile rules
  mkFile "out.dl" $ result
