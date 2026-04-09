{-# LANGUAGE PatternSynonyms #-}
module Types where

import Control.Monad.State
import Data.Functor.Identity
import Data.Monoid (Sum(..))
import Data.Char
import Data.List
import qualified MMap as M
import MMap (MMap)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String
import Data.Maybe

import Basic

type Name = String
data Global = Global Name Name
-- TODO: still needed?
data Var = FreeVar Name | PosVar Name | ExVar Name
  deriving (Show, Eq, Ord)
isFreeVar = \case FreeVar _ -> True; _ -> False
isPosVar = \case PosVar _ -> True; _ -> False
isExVar = \case ExVar _ -> True; _ -> False
varName = \case
    FreeVar v -> v
    PosVar v -> v
    ExVar  v -> v
data Id = Id Name [Var]
  deriving (Show, Eq, Ord)
data Pred = Pred String
  deriving (Show, Eq, Ord)
data T = L Term | R Term | Min T T | Max T T | Top | Bot
  deriving (Show, Eq, Ord)
data I = I T T deriving (Show, Eq, Ord)
data BinOp = BinAdd | BinSub deriving (Show, Eq, Ord)
data Term = TermPred Pred
          | TermNum Int
          | TermId Id
          | TermVar Var
          | TermFreshVar Var
          | TermChoiceVar (Maybe Var) Var
          | TermBlank
          | TermExt String
          | TermApp Name [Term]
          | TermBin BinOp Term Term
  deriving (Show, Eq, Ord)

data Op = OpLt
        | OpEq
  deriving (Show, Eq, Ord)
data AtomType
  = AtomFree
  | AtomPos
  | AtomAsk
  | AtomNeg
  deriving (Show, Eq, Ord)

data PVar = PVar { pvar :: Maybe Var, pname :: Maybe Name }
  deriving (Show, Eq, Ord)
         -- , pdeps :: Maybe [Var]

pattern NoVars = PVar Nothing Nothing
pattern AllVars a c = PVar (Just a) (Just c)

data Pattern = Pattern { ty :: AtomType, id :: PVar, terms :: [Term] }
  deriving (Show, Eq, Ord)

pattern PP p ts <- Pattern _ _ (TermPred p : ts)
pattern PPI p s i ts <- Pattern s (PVar (Just i) _) (TermPred p : ts)
pattern PPP p a b ts = Pattern a b (TermPred p : ts)

data EndpointCmp = ECLt | ECGt | ECEq | ECNone
  deriving (Show, Eq, Ord)

data E = Atom Pattern
       | EVar Term
       | After E

       | GenAnd EndpointCmp EndpointCmp E E
       | Seq E E
       | Par E E
       | Over E E
       | Under E E
       | At E E
       | And E E -- ~~
       | Same E E -- ==
       | SameIsh E E -- ~=

       | Instead Pattern E
       | SameNot E Pattern
  deriving (Show, Eq, Ord)

data Constraint
  = Constraint Pattern
  | Cmp Op T T
  | Eq Term Term
  | Other [Term]
  | Not [Constraint]
  -- TODO: remove these
  | IsId Term
  | Val Term Term
  | Try Pattern
  deriving (Show, Eq, Ord)

pattern Lt a b = Cmp OpLt a b
pattern Eql a b = Cmp OpEq a b

data TRule = TRule { trName :: Name, trE :: E }
  deriving Show

trMap f (TRule n e) = TRule n (f e)

-- todo: generate count summary for each Pragma
data Statement = Pragma Pred | RuleStatement (Maybe Name) E
  deriving (Show, Eq, Ord)

-- Compiler Output
data Rule = Rule { body :: Set Constraint, head :: Set Constraint }
  deriving (Show, Eq, Ord)

type Ms b c a = (State (MMap b c)) a
type M a = Ms String (Sum Int) a
type MonadFreshVarState m = MonadState (MMap String (Sum Int)) m

noPVar = PVar Nothing Nothing

opIneq = \case
  OpLt -> True
  OpEq -> False

isPositive AtomPos = True
isPositive AtomFree = False
isPositive AtomAsk = False
isPositive AtomNeg = False

evalM m = evalState m M.empty

fresh :: (MonadFreshVarState m) => String -> m Name
fresh t = do
  Sum i <- gets (M.lookup t);
  modify (M.insert t 1)
  pure $ t <> show i

fixId = map fix
    where
      fix '-' = '-'
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
  pp Bot = "⊥"
instance PP Pred where
  pp (Pred s) = fixId s
instance PP Var where
  pp = fixId . \case
    FreeVar v -> v
    PosVar v -> v
    ExVar v -> "-" <> v
instance PP BinOp where
  pp BinAdd = "+"
  pp BinSub = "-"
instance PP Term where
  pp (TermVar v) = pp v
  pp (TermPred p) = pp p
  pp (TermNum i) = show i
  pp (TermId i) = pp i
  pp (TermFreshVar v) = "!" <> pp v
  pp (TermChoiceVar _ v) = "?" <> pp v
  pp (TermExt s) = s
  pp TermBlank = "_"
  pp (TermApp c ts) = c <> args (map pp ts)
  pp (TermBin op a b) = pwrap $ pp a <> pp op <> pp b
instance PP AtomType where
  pp AtomFree = "?"
  pp AtomPos = "!"
  pp AtomAsk = "∃"
  pp AtomNeg = "¬"
instance PP PVar where
  pp NoVars = ""
  pp (PVar pv _mn) = bwrap $ mpp pv -- <> "=" <> mpp (do { n <- mn; vs <- pvs; pure $ Id n vs })
    where
      mpp :: PP a => Maybe a -> String
      mpp = maybe "" pp
instance PP Pattern where
  pp (Pattern sign pv c) =
    pp sign <> pp pv <> (unwords . map pp $ c)
instance PP Constraint where
  pp (Constraint p) = pp p
  pp (Other ts) = pp ts
  pp (Cmp op a b) = pp a <> spwrap (pp op) <> pp b
  pp (Eq a b) = pp a <> spwrap "=" <> pp b
  pp (Val a b) = "Val " <> pp a <> " " <> pp b
  pp (IsId t) = "IsId " <> pp t
  pp (Try t) = "Try " <> pp t
  pp (Not cs) = "!" <> args (map pp cs)
instance PP Op where
  pp OpLt = "<"
  pp OpEq = "="
instance PP EndpointCmp where
  pp = \case
    ECEq -> "="
    ECLt -> "<"
    ECGt -> ">"
    ECNone -> "~"
instance PP E where
  pp (Atom p) = pp p
  pp (After e) = "#" <> pp e
  pp (EVar e) = pp e
  pp (GenAnd l r a b) = pwrap $ pp a <> " " <> pp l <> pp r <> " " <> pp b
  pp (And a b) = pwrap $ pp a <> ", " <> pp b
  pp (Seq a b) = pwrap $ pp a <> "; " <> pp b
  pp (Par a b) = pwrap $ pp a <> " | " <> pp b
  pp (Over a b) = pwrap $ pp a <> " / " <> pp b
  pp (Under a b) = pwrap $ pp a <> " \\ " <> pp b
  pp (Same a b) = pwrap $ pp a <> " ~ " <> pp b
  pp (At a b) = pwrap $ pp a <> " @ " <> pp b
  pp (SameIsh a b) = pwrap $ pp a <> " ~> " <> pp b
  pp (Instead a b) = pwrap $ pp a <> " -> " <> pp b
  pp (SameNot a b) = pwrap $ pp a <> " ~¬ " <> pp b
instance PP TRule where
  pp (TRule n e) = n <> ": " <> pp e <> "."
instance PP Statement where
  pp (RuleStatement mname e) = maybe "" (pp .> (<> ": ")) mname <> pp e
  pp (Pragma p) = '#' : pp p -- todo

tryPred = "try__"
chosePred = "chose__"

eTraverse :: Applicative m => (E -> m E) -> E -> m E
eTraverse f = go
  where
    go e@(Atom _) = f e
    go e@(EVar _) = f e
    go e@(Instead _ _) = f e -- TODO
    go (After e) = (After <$> go e)
    go (GenAnd l r a b) = GenAnd l r <$> (go a) <*> (go b)
    go (And a b) = And <$> (go a) <*> (go b)
    go (Seq a b) = Seq <$> (go a) <*> (go b)
    go (Par a b) = Par <$> (go a) <*> (go b)
    go (Over a b) = Over <$> (go a) <*> (go b)
    go (Under a b) = Under <$> (go a) <*> (go b)
    go (Same a b) = Same <$> (go a) <*> (go b)
    go (At a b) = At <$> (go a) <*> (go b)
    go (SameIsh a b) = SameIsh <$> (go a) <*> (go b)
    go (SameNot a b) = SameNot <$> (go a) <*> pure b

eMap :: (E -> E) -> E -> E
eMap f = runIdentity . eTraverse (pure . f)

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
    go Bot = f Bot
    go (Min a b) = Min <$> go a <*> go b
    go (Max a b) = Max <$> go a <*> go b

patternVars (Pattern _ (PVar i _) ts) = maybeToList i <> termsVars ts
termsVars = concatMap termVars
termVars (TermVar v) = [v]
termVars (TermChoiceVar _ v) = [v]
termVars (TermApp _ ts) = termsVars ts
termVars (TermBin _ a b) = termsVars [a,b]
termVars (TermFreshVar _) = [] -- these elaborate directly into an id constructor
termVars (TermId (Id _ vs)) = vs -- should be redundant
termVars (TermPred {}) = []
termVars (TermExt _) = []
termVars (TermNum _) = []
termVars TermBlank = []
constraintVars (Constraint p) = patternVars p
constraintVars (Other ts) = termsVars ts
constraintVars (Cmp _ a b) = tVars a <> tVars b
constraintVars (IsId t) = termVars t
constraintVars (Eq a b) = termVars a <> termVars b
constraintVars (Val a b) = termVars a <> termVars b
constraintVars (Not cs) = concatMap constraintVars cs
constraintVars (Try _) = error "todo"
constraintsVars :: [Constraint] -> [Var]
constraintsVars = concatMap constraintVars
tVars (L t) = termVars t
tVars (R t) = termVars t
tVars (Min a b) = tVars a <> tVars b
tVars (Max a b) = tVars a <> tVars b
tVars Top = []
tVars Bot = []

-- special predicate names
pattern PredIsId = "is-id"
