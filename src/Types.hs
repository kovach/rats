{-# LANGUAGE PatternSynonyms #-}
module Types where

import Control.Monad.State
import Data.Monoid (Sum(..))
import Data.Char
import Data.List
import qualified MMap as M
import MMap (MMap)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String

import Basic

type Name = String
data Var = NegVar Name | PosVar Name | ExVar Name
  deriving (Show, Eq, Ord)
isNegVar = \case NegVar _ -> True; _ -> False
isPosVar = \case PosVar _ -> True; _ -> False
isExVar = \case ExVar _ -> True; _ -> False
varName = \case
    NegVar v -> v
    PosVar v -> v
    ExVar v ->  v
data Id = Id Name [Var]
  deriving (Show, Eq, Ord)
data Pred = Pred String
  deriving (Show, Eq, Ord)
data T = L Term | R Term | Min T T | Max T T | Top
  deriving (Show, Eq, Ord)
data I = I T T deriving (Show, Eq, Ord)
data Term = TermPred Pred
          | TermId Id
          | TermVar Var
          | TermFreshVar Var
          | TermChoiceVar (Maybe Var) Var
          | TermBlank
          | TermExt String
  deriving (Show, Eq, Ord)

data Op = OpLt
        | OpEq
  deriving (Show, Eq, Ord)
opIneq = \case
  OpLt -> True
  OpEq -> False
data AtomType
  = AtomNeg
  | AtomPos
  deriving (Show, Eq, Ord)

isPositive AtomPos = True
isPositive AtomNeg = False

data PVar
  = PVar2 Var [Var] Name
  | PVar0
  deriving (Show, Eq, Ord)

data Pattern
  = Pattern { ty :: AtomType, id :: PVar, terms :: [Term] }
  | Cmp Op T T
  | Eq Term Term
  | IsId Term
  | Val Term Term
  deriving (Show, Eq, Ord)

--pattern IdPattern ty i terms = Pattern ty (Just i) terms

data E = Atom Pattern
       | EVar Term
       | After E
       | And E E
       | Seq E E
       | Par E E
       | Over E E
       | Same E E
       | At E E
       | Under E E
       -- | Count Name E
  deriving (Show, Eq, Ord)

-- todo: generate count summary for each Pragma
data Statement = Pragma Pred | Rule (Maybe Name) E
  deriving (Show, Eq, Ord)

type Ms b c a = (State (MMap b c)) a
type M a = Ms String (Sum Int) a
evalM m = evalState m M.empty

type MonadFreshVarState m = MonadState (MMap String (Sum Int)) m

fresh :: (MonadFreshVarState m) => String -> m Name
fresh t = do
  Sum i <- gets (M.lookup t);
  modify (M.insert t 1)
  pure $ t <> show i -- (if i == 0 then "" else show i)

fixId = map fix
    where
      fix '-' = '_'
      fix x = x
instance IsString Pred where
  fromString = Pred

instance PP Id where pp (Id n vs) = n <> bwrap (unwords $ map pp vs)
instance PP T where
  pp (L t) = pp t <> "□"
  pp (R t) = pp t <> "∎"
  pp (Min a b) = "min(" <> pp a <> ", " <> pp b <> ")"
  pp (Max a b) = "max(" <> pp a <> ", " <> pp b <> ")"
  pp Top = "⊤"
instance PP Pred where
  pp (Pred s) = fixId s
instance PP Var where
  pp = fixId . \case
    NegVar v -> v
    PosVar v -> v
    ExVar v -> "-" <> v
instance PP Term where
  pp (TermVar v) = pp v
  pp (TermPred p) = pp p
  pp (TermId i) = pp i
  pp (TermFreshVar v) = "!" <> pp v
  pp (TermChoiceVar _ v) = "?" <> pp v
  pp (TermExt s) = s
  pp TermBlank = "_"
instance PP AtomType where
  pp AtomNeg = "?"
  pp AtomPos = "!"
instance PP Pattern where
  pp (Pattern sign PVar0 c) = pp sign <> (pwrap . unwords . map pp $ c)
  pp (Pattern sign (PVar2 i vs n) c) =
    pp sign <> pwrap (pp i <> "=" <> pp (Id n vs)) <> ":"
    <> (pwrap . unwords . map pp $ c)
  pp (Cmp op a b) = pp a <> spwrap (pp op) <> pp b
  pp (Eq a b) = pp a <> spwrap "=" <> pp b
  pp (Val a b) = "Val " <> pp a <> " " <> pp b
  pp (IsId t) = "IsId " <> pp t
instance PP Op where
  pp OpLt = "<"
  pp OpEq = "="
instance PP E where
  pp (Atom p) = pp p
  pp (After e) = ">" <> pp e
  pp (EVar e) = pp e
  pp (And a b) = pwrap $ pp a <> ", " <> pp b
  pp (Seq a b) = pwrap $ pp a <> "; " <> pp b
  pp (Par a b) = pwrap $ pp a <> " | " <> pp b
  pp (Over a b) = pwrap $ pp a <> " / " <> pp b
  pp (Under a b) = pwrap $ pp a <> " \\ " <> pp b
  pp (Same a b) = pwrap $ pp a <> " ~ " <> pp b
  pp (At a b) = pwrap $ pp a <> " @ " <> pp b

eTraverse :: Applicative m => (E -> m E) -> E -> m E
eTraverse f = go
  where
    go e@(Atom _) = f e
    go e@(EVar _) = f e
    go (After e) = After <$> go e
    go (And a b) = And <$> (go a) <*> (go b)
    go (Seq a b) = Seq <$> (go a) <*> (go b)
    go (Par a b) = Par <$> (go a) <*> (go b)
    go (Over a b) = Over <$> (go a) <*> (go b)
    go (Under a b) = Under <$> (go a) <*> (go b)
    go (Same a b) = Same <$> (go a) <*> (go b)
    go (At a b) = At <$> (go a) <*> (go b)

eTraverse' :: Applicative m => (E -> m ()) -> E -> m ()
eTraverse' f e0 = eTraverse (\e -> f e *> pure e) e0 *> pure ()

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
