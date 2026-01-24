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

type Name = String
data Var = Blank | Var Name | CVar Name
  deriving (Show, Eq, Ord)
data Id = Id Name [Var]
  deriving (Show, Eq, Ord)
data Pred = Pred String
  deriving (Show, Eq, Ord)
data T = L Term | R Term | Min T T | Max T T | Top
  deriving (Show, Eq, Ord)
data I = I T T deriving (Show, Eq, Ord)
data Term = TermPred Pred
          | TermVar Var
          | TermFreshVar String
          | TermId Id
          | TermAfter Term -- todo remove
          | TermExt String
  deriving (Show, Eq, Ord)

data Op = OpLt | OpLe | OpEq deriving (Show, Eq, Ord)
data AtomType
  = AtomDuring
  | AtomAfter
  | AtomPos
  deriving (Show, Eq, Ord)

data Pattern
  = Pattern { ty :: AtomType, terms :: [Term] }
  | IdPattern { id :: Term, terms :: [Term] }
  | Cmp Op T T
  | IsId Term
  deriving (Show, Eq, Ord)

data E = Atom Pattern
       | After E
       | Fresh Name
       | And E E
       | Seq E E
       | Par E E
       | Over E E
       | Same E E
  deriving (Show, Eq, Ord)

data Statement = Pragma Pred | Rule E
  deriving (Show, Eq, Ord)

pwrap x = "(" <> x <> ")"
bwrap x = "[" <> x <> "]"
spwrap x = " " <> x <> " "

class PP a where
  pp  :: a -> String

instance (PP a, PP b) => PP (a, b) where
  pp (a,b) = "(" <> pp a <> ", " <> pp b <> ")"

instance PP a => PP [a] where
  pp xs = "[" <> intercalate ", " (map pp xs) <> "]"

instance PP a => PP (Set a) where
  pp xs = "[" <> intercalate ", " (Set.toList $ Set.map pp xs) <> "]"

--instance (PP a, Traversable f) => PP (f a) where
--  pp xs = "[" <> intercalate ", " (map pp $ traverse (\a -> [a]) xs) <> "]"

pprint :: PP a => a -> IO ()
pprint = putStrLn . pp

assert a b | a == b = putStrLn "ok"
assert a b = error $ "not-equal:\n" <> pp a <> "\n\n" <> pp b

capitalize = map toUpper

type Ms b c a = (State (MMap b c)) a
type M a = Ms String (Sum Int) a
evalM m = evalState m M.empty

type MonadFreshVarState m = MonadState (MMap String (Sum Int)) m

fresh :: (MonadFreshVarState m) => String -> m String
fresh t = do
  Sum i <- gets (M.lookup t);
  modify (M.insert t 1)
  pure $ t <> (if i == 0 then "" else show i)

instance IsString Pred where
  fromString = Pred

instance PP Id where pp (Id n vs) = n <> bwrap (unwords $ map pp vs)
instance PP T where
  pp (L t) = pp t <> "□"
  pp (R t) = pp t <> "∎"
  --pp t = show t
  pp (Min a b) = "min(" <> pp a <> ", " <> pp b <> ")"
  pp (Max a b) = "max(" <> pp a <> ", " <> pp b <> ")"
  pp Top = "⊤"
instance PP Pred where pp (Pred s) = s
instance PP Var where
  pp = \case { Var v -> v; CVar cv -> cv; Blank -> "_" }
instance PP Term where
  pp (TermVar v) = pp v
  pp (TermPred p) = pp p
  pp (TermId i) = pp i
  pp (TermAfter i) = ">" <> pp i
  pp (TermFreshVar v) = "!" <> v
  pp (TermExt s) = s
instance PP Pattern where
  pp (Pattern AtomDuring c) = "?" <> (pwrap . unwords . map pp $ c)
  pp (Pattern AtomAfter c) = ">" <> (pwrap . unwords . map pp $ c)
  pp (Pattern AtomPos c) = "!" <> (pwrap . unwords . map pp $ c)
  pp (IdPattern i c) = pp i <> ":" <> (pwrap . unwords . map pp $ c)
  pp (Cmp op a b) = pp a <> spwrap (pp op) <> pp b
  pp (IsId t) = "IsId " <> pp t
instance PP Op where
  pp OpLt = "<"
  pp OpLe = "≤"
  pp OpEq = "="
instance PP E where
  pp (Atom p) = pp p
  pp (Fresh n) = "!" <> n
  pp (After e) = ">" <> pp e
  pp (And a b) = pwrap $ pp a <> ", " <> pp b
  pp (Seq a b) = pwrap $ pp a <> "; " <> pp b
  pp (Par a b) = pwrap $ pp a <> " | " <> pp b
  pp (Over a b) = pwrap $ pp a <> " / " <> pp b
  pp (Same a b) = pwrap $ pp a <> " ~ " <> pp b
