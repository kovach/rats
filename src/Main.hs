{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Main where

import Control.Monad.State
import Control.Monad.Writer
import Data.Functor.Identity
import Data.String
import Data.List

import Types

data Var = Blank | Var String | CVar String
  deriving (Show, Eq, Ord)
type Name = String
data Id = Id Name [Var]
  deriving (Show, Eq, Ord)
data Pred = Pred String
  deriving (Show, Eq, Ord)
data T = L Term | R Term | Min T T | Max T T
  deriving (Show, Eq, Ord)
data I = I T T deriving (Show, Eq, Ord)
data Term = TermPred Pred | TermVar Var | TermId Id | TermT T
  deriving (Show, Eq, Ord)
data Op = OpLt | OpLe deriving (Show, Eq, Ord)
data AtomType = AtomNeg | AtomPos
  deriving (Show, Eq, Ord)
data Pattern
  = Pattern { ty :: AtomType, terms :: [Term] }
  | IdPattern { id :: Term, terms :: [Term] }
  | Cmp Op T T
  deriving (Show, Eq, Ord)
data Rule = Rule { name :: String, body :: [Pattern], head :: [Pattern] }
  deriving (Show, Eq, Ord)

predString (Pred s) = s
predPattern (Pattern _ (TermPred p : ts)) = p
pVars (Pattern _ ts) = varTerms ts
pVars (IdPattern i ts) = varTerms (i:ts)
varTerms = concatMap tVars
tVars (TermVar v) = [v]
tVars (TermId (Id _ vs)) = vs
tVars _ = []
instance IsString Pred where
  fromString = Pred

data A = Assertion Pattern
  -- | Choice Pattern -- maybe not
  -- | Constraint Pattern
data Q = Query Pattern

data E
  = Atom Pattern
  | And E E
  | Seq E E
  | Par E E
  | Over E E
  -- sym, `@`?
  deriving (Show, Eq, Ord)

pattern Lt a b = Cmp OpLt a b
pattern Le a b = Cmp OpLe a b
--pattern Cmp op a b = Pattern [TermPred op, TermT a, TermT b]
pattern NegAtom ts = Atom (Pattern AtomNeg ts)
pattern PosAtom ts = Atom (Pattern AtomPos ts)
pattern IdAtom i ts = Atom (IdPattern i ts)


-- tell :: w -> Writer w ()
-- pure :: a -> Writer w a
--
check :: E -> Writer [Pattern] I
check (Atom p@(IdPattern i _)) = do tell [p, Lt (L i) (R i)]; pure (I (L i) (R i))
check (Atom p) = error $ pp p
check (Par e1 e2) = do
  I l1 r1 <- check e1
  I l2 r2 <- check e2
  pure $ I (Min l1 l2) (Max r1 r2)
check (And a b) = do
  I aLeft aRight <- check a
  I bLeft bRight <- check b
  tell [Max aLeft bLeft `Lt` Min aRight bRight]
  pure $ I (Max aLeft bLeft) (Min aRight bRight)
check (Seq e1 e2) = do
  I l1 r1 <- check e1
  I l2 r2 <- check e2
  tell [r1 `Le` l2]
  pure $ I l1 r2
check (Over e1 e2) = do
  I l1 r1 <- check e1
  I l2 r2 <- check e2
  tell [l1 `Lt` l2, r2 `Lt` r1]
  pure $ I l1 r2

checkAll :: E -> [Pattern]
checkAll = snd . runWriter . check

expandConstraints :: [Pattern] -> [Pattern]
expandConstraints = concatMap expandConstraint
expandConstraint :: Pattern -> [Pattern]
expandConstraint (Cmp op (Max a b) c) = expandConstraints [Cmp op a c, Cmp op b c]
expandConstraint (Cmp op a (Min b c)) = expandConstraints [Cmp op a b, Cmp op a c]
expandConstraint p@(Cmp _ (Min _ _) _) = error $ pp p
expandConstraint p@(Cmp _ _ (Max _ _)) = error $ pp p
-- todo
expandConstraint x = [x]

termContainsId (TermId _) = True
termContainsId (TermT t) = tContainsId t
termContainsId _ = False
tContainsId = \case
  L t' -> termContainsId t'
  R t' -> termContainsId t'
  Min t1 t2 -> tContainsId t1 || tContainsId t2
  Max t1 t2 -> tContainsId t1 || tContainsId t2

isPos :: Pattern -> Bool
isPos (IdPattern i ts) = any termContainsId (i:ts)
isPos (Cmp _ a b) = any tContainsId [a,b]
isPos (Pattern {}) = error ""

splitConstraints x =
  let (pos, neg) = partition isPos x
   in (neg, pos)


chk = splitConstraints . nub . expandConstraints . checkAll . elab

pwrap x = "(" <> x <> ")"
bwrap x = "[" <> x <> "]"
instance PP Id where pp (Id n vs) = n <> bwrap (unwords $ map pp vs)
instance PP T where
  pp (L t) = pp t <> "□"
  pp (R t) = pp t <> "∎"
  --pp t = show t
  pp (Min a b) = "min(" <> pp a <> ", " <> pp b <> ")"
  pp (Max a b) = "max(" <> pp a <> ", " <> pp b <> ")"
instance PP Pred where pp (Pred s) = s
instance PP Var where
  pp = \case { Var v -> v; CVar cv -> cv; Blank -> "_" }
instance PP Term where
  pp (TermVar v) = pp v
  pp (TermPred p) = pp p
  pp (TermId i) = pp i
  pp (TermT t) = pp t
instance PP Pattern where
  --pp (PredPattern p []) = pp p
  pp (Pattern AtomNeg c) = "?" <> (pwrap . unwords . map pp $ c)
  pp (Pattern AtomPos c) = "!" <> (pwrap . unwords . map pp $ c)
  pp (IdPattern id c) = pp id <> ":" <> (pwrap . unwords . map pp $ c)
  pp (Cmp OpLt a b) = pp a <> " < " <> pp b
  pp (Cmp OpLe a b) = pp a <> " ≤ " <> pp b
instance PP E where
  pp (Atom p) = pp p
  pp (And a b) = pwrap $ pp a <> ", " <> pp b
  pp (Seq a b) = pwrap $ pp a <> "; " <> pp b
  pp (Par a b) = pwrap $ pp a <> " | " <> pp b
  pp (Over a b) = pwrap $ pp a <> " / " <> pp b

mtraverse :: Monad m => (E -> m E) -> E -> m E
mtraverse f = go
  where
    go a@(Atom{}) = f a
    go (And a b)  = do a' <- go a; b' <- go b; f $ And a' b'
    go (Seq a b)  = do a' <- go a; b' <- go b; f $ Seq a' b'
    go (Par a b)  = do a' <- go a; b' <- go b; f $ Par a' b'
    go (Over a b) = do a' <- go a; b' <- go b; f $ Over a' b'

traverse :: (E -> E) -> E -> E
traverse f = runIdentity . mtraverse (pure . f)

negUnary x = Atom (Pattern AtomNeg [TermPred (Pred x)])
posUnary x = Atom (Pattern AtomPos [TermPred (Pred x)])

type M a = (State Int) a
evalM m = evalState m 0

fresh :: String -> M Name
fresh t = do
  s <- get;
  modify (+1);
  pure $ t <> show s

freshAtomVar p = fresh $ capitalize $ predString $ predPattern p
freshAtomVar _ = fresh "_id"

vars :: E -> [Var]
vars = snd . runWriter . mtraverse go
  where
    go a@(IdAtom t p) = do tell (tVars t); tell (varTerms p); pure a
    go a@(Atom p) = do tell (pVars p); pure a
    go x = pure x

elabNeg = evalM .  mtraverse go
  where
    go (Atom p@(Pattern AtomNeg ts)) = do
      m <- freshAtomVar p;
      pure $ Atom (IdPattern (TermVar (Var m)) ts)
    go x = pure x

elabPos e = evalM $ mtraverse go e
  where
    vs = vars e
    go (Atom p@(Pattern AtomPos ts)) = do
      m <- freshAtomVar p;
      pure (IdAtom (TermId (Id m vs)) ts)
    go x = pure x

elab = elabPos . elabNeg

-- a, b
-- ----
-- c; d
e1 =
  let q = And (negUnary "a") (negUnary "b")
      h = Seq (posUnary "c") (posUnary "d")
  in Over q h

-- collect schema from rules
-- each body pattern gets an I-var
-- each head pattern gets an I-val (constructed)

--overlap :: Pattern -> Pattern -> [Pattern]
--overlap = _
--compileBody :: Rule -> Writer [Pattern] ()
--compileBody (Rule {body}) =
--    mapM_  (\(c1, c2) -> tell $ overlap c1 c2)
--    (pairs body body)

--c1 :: IO ()
--c1 = do
--    prelude <- readFile "prelude.dl"
--    writeFile "main.dl" $ prelude <> str
--  where
--    prefix = ".decl P(x: Id) .output P"
--    str = unlines $ [prefix, compile r1]
--    compile (Rule r [] [Pattern [TermPred (Pred p)]]) = head <> ":-" <> body <> "."
--      where
--        body = var <> "=[\""<> r <>"\", $Nil()]"
--        head = p <> "(" <> var <> ")"
--        var = "j"
--    r1 = Rule "r1" [] [Pattern [TermPred (Pred "P")]]

pprint :: PP a => a -> IO ()
pprint = putStrLn . pp
main = do
  pprint $ e1
  putStrLn "---------"
  pprint $ elab e1
  putStrLn "---------"
  let (body, head) = chk e1
  mapM_ pprint body
  putStrLn "---------"
  mapM_ pprint head
