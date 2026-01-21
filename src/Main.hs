{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main, emap) where

import Control.Monad.Writer
import Data.Functor.Identity
import Data.String
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

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
data AtomType = AtomNeg | AtomPos deriving (Show, Eq, Ord)
data Pattern
  = Pattern { ty :: AtomType, terms :: [Term] }
  | IdPattern { id :: Term, terms :: [Term] }
  | Cmp Op T T
  deriving (Show, Eq, Ord)
data Rule = Rule { name :: String, body :: [Pattern], head :: [Pattern] }
  deriving (Show, Eq, Ord)

predString (Pred s) = s
predPattern :: Pattern -> Maybe Pred
predPattern (Pattern _ (TermPred p : _)) = Just p
predPattern _ = Nothing
pVars (Pattern _ ts) = varTerms ts
pVars (IdPattern i ts) = varTerms (i:ts)
varTerms = concatMap tVars
tVars (TermVar v) = [v]
tVars (TermId (Id _ vs)) = vs
tVars _ = []
instance IsString Pred where
  fromString = Pred

data E = Atom Pattern
       | And E E
       | Seq E E
       | Par E E
       | Over E E
  deriving (Show, Eq, Ord)

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

emap :: (E -> E) -> E -> E
emap f = runIdentity . eFoldM (pure . f)

negUnary x = Atom (Pattern AtomNeg [TermPred (Pred x)])
posUnary x = Atom (Pattern AtomPos [TermPred (Pred x)])

freshAtomVar p | Just pr <- predPattern p = fresh $ capitalize $ predString pr
freshAtomVar _ = fresh "_id"

vars :: E -> [Var]
vars = snd . runWriter . eTraverse go
  where
    go p = do tell (pVars p); pure (Atom p)

elabNeg = evalM .  eFoldM go
  where
    go (Atom p@(Pattern AtomNeg ts)) = do
      m <- freshAtomVar p;
      pure $ Atom (IdPattern (TermVar (Var m)) ts)
    go x = pure x

elabPos e = evalM $ eFoldM go e
  where
    vs = vars e
    go (Atom p@(Pattern AtomPos ts)) = do
      m <- freshAtomVar p;
      pure (IdAtom (TermId (Id m vs)) ts)
    go x = pure x

elab = elabPos . elabNeg

check :: E -> Writer [Pattern] I
check (Atom p@(IdPattern i _)) = do tell [p, Lt (L i) (R i)]; pure (I (L i) (R i))
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

expandConstraints :: [Pattern] -> [Pattern]
expandConstraints = concatMap expandConstraint
expandConstraint :: Pattern -> [Pattern]
expandConstraint (Cmp op (Max a b) c) = expandConstraints [Cmp op a c, Cmp op b c]
expandConstraint (Cmp op a (Min b c)) = expandConstraints [Cmp op a b, Cmp op a c]
expandConstraint p@(Cmp _ (Min _ _) _) = error $ pp p  -- no disjunctive comparisons
expandConstraint p@(Cmp _ _ (Max _ _)) = error $ pp p  -- no disjunctive comparisons
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
   in (Set.fromList neg, Set.fromList pos)

chk = splitConstraints . nub . expandConstraints . checkAll . elab
-- format and print constraints as souffle
--   print any type declarations needed

pwrap x = "(" <> x <> ")"
bwrap x = "[" <> x <> "]"

-- (a, b) / (c; d)
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

e1 =
  let q = And (negUnary "a") (negUnary "b")
      h = Seq (posUnary "c") (posUnary "d")
  in Over q h
expect = (Set.fromList [IdPattern {id = TermVar (Var "A"), terms = [TermPred (Pred "a")]},IdPattern {id = TermVar (Var "B"), terms = [TermPred (Pred "b")]},Cmp OpLt (L (TermVar (Var "A"))) (R (TermVar (Var "A"))),Cmp OpLt (L (TermVar (Var "A"))) (R (TermVar (Var "B"))),Cmp OpLt (L (TermVar (Var "B"))) (R (TermVar (Var "A"))),Cmp OpLt (L (TermVar (Var "B"))) (R (TermVar (Var "B")))],Set.fromList [IdPattern {id = TermId (Id "C" [Var "A",Var "B"]), terms = [TermPred (Pred "c")]},IdPattern {id = TermId (Id "D" [Var "A",Var "B"]), terms = [TermPred (Pred "d")]},Cmp OpLt (L (TermVar (Var "A"))) (L (TermId (Id "C" [Var "A",Var "B"]))),Cmp OpLt (L (TermVar (Var "B"))) (L (TermId (Id "C" [Var "A",Var "B"]))),Cmp OpLt (L (TermId (Id "C" [Var "A",Var "B"]))) (R (TermId (Id "C" [Var "A",Var "B"]))),Cmp OpLt (L (TermId (Id "D" [Var "A",Var "B"]))) (R (TermId (Id "D" [Var "A",Var "B"]))),Cmp OpLt (R (TermId (Id "D" [Var "A",Var "B"]))) (R (TermVar (Var "A"))),Cmp OpLt (R (TermId (Id "D" [Var "A",Var "B"]))) (R (TermVar (Var "B"))),Cmp OpLe (R (TermId (Id "C" [Var "A",Var "B"]))) (L (TermId (Id "D" [Var "A",Var "B"])))])
main = do
  pprint $ e1
  putStrLn "---------"
  pprint $ elab e1
  putStrLn "---------"
  let p@(body, h) = chk e1
  mapM_ pprint body
  putStrLn "---------"
  mapM_ pprint h
  assert p expect
