-- "DERiving Predicates"
module Derp where

import Data.Maybe
import Control.Monad hiding (join)
import Data.Set (Set)
import Data.List
import qualified Data.Set as Set

import Basic
import qualified Binding as B

type Name = String
type Pred = String
data Id = Id { rule :: Name, bound :: [Term] }
  deriving (Show, Eq, Ord)
data Term
  = TermVar Name
  | TermPred Pred
  | TermNum Int
  | TermId Id
  | TermBlank
  | TermApp Name [Term]
  deriving (Show, Eq, Ord)

data E
  = Join E E
  | Leaf [Term]
  | Bind Name Term
  | Unit
  deriving (Show, Eq, Ord)

type Binding = B.Binding Name Term

data Closure a = Closure { context :: Binding, clVal :: a }
  deriving (Show, Eq, Ord, Functor)
type CE = Closure E

data Rule = Rule { body :: CE, head :: [Tuple] }
  deriving (Show, Eq, Ord)

instance B.Unify Binding Term Term where
  unify b TermBlank _ = pure b
  unify b _ TermBlank = pure b
  unify b (TermVar var) v  = B.unify b var v
  unify b l@(TermPred _) r = guard (l == r) >> pure b
  unify b l@(TermNum _) r  = guard (l == r) >> pure b
  unify b l@(TermId _) r   = guard (l == r) >> pure b
  unify b (TermApp cons ts) (TermApp cons' ts') = do
    guard $ cons == cons'
    B.unify b ts ts'
  unify _ (TermApp {}) _ = fail "app"

instance B.Unify Binding [Term] [Term] where
  unify b ts ts' = do
    guard (length ts == length ts')
    foldM (uncurry . B.unify) b $ zip ts ts'

join Unit x = x
join x Unit = x
join x y = Join x y

leaf [] = Unit
leaf t = Leaf t

joins :: Foldable f => f Tuple -> E
joins = foldr (\x acc -> join (leaf x) acc) Unit
joins' :: Foldable f => f E -> E
joins' = foldr (\x acc -> join x acc) Unit

type Tuple = [Term]
specialize :: CE -> Tuple -> [CE]
specialize e@(Closure _ Unit) _ = [e]
specialize (Closure _ Bind{}) _ = []
specialize (Closure b (Leaf pat)) tuple = do
  b' <- maybeToList $ B.unify b pat tuple
  pure $ Closure b' Unit
specialize (Closure c (Join a b)) tuple = left <> right <> both
  where
    spec ct x = specialize (Closure ct x) tuple
    left = do
      Closure c' a' <- spec c a
      pure $ Closure c' (join a' b)
    right = do
      Closure c' b' <- spec c b
      pure $ Closure c' (join a b')
    both = do
      Closure c' a' <- spec c a
      Closure c'' b' <- spec c' b
      pure $ Closure c'' (join a' b')

eval :: CE -> [Tuple] -> [Binding]
eval (Closure b Unit) _ = [b]
eval (Closure b (Bind v t)) _ = [B.extend b v (subTerm b t)]
eval c@(Closure _ (Leaf _)) tuples = concatMap (map context . specialize c) tuples
eval (Closure c (Join a b)) tuples = do
  c' <- eval (Closure c a) tuples
  c'' <- eval (Closure c' b) tuples
  pure c''

eval1 :: CE -> Tuple -> [Tuple] -> [Binding]
eval1 cl t ts = do
  cl' <- specialize cl t
  v <- eval cl' ts
  pure v

subTerm ctx = \case
    TermVar n -> fromJust $ B.lookup n ctx
    TermApp cons ts -> TermApp cons (map (subTerm ctx) ts)
    TermBlank -> error ""
    x -> x

subst ctx tuple = map sub1 tuple
  where
    sub1 (TermVar n) = fromJust $ B.lookup n ctx
    sub1 (TermApp cons ts) = TermApp cons (map sub1 ts)
    sub1 TermBlank = error ""
    sub1 x = x

step :: Rule -> Tuple -> Set Tuple -> [Tuple]
step (Rule body hd) t ts = do
  ctx <- eval1 body t (Set.toList ts)
  map (subst ctx) hd

evalRule :: Rule -> Set Tuple -> [Tuple]
evalRule (Rule body hd) ts = do
  ctx <- eval body (Set.toList ts)
  map (subst ctx) hd

iter :: Ord a => (a -> Set a -> [a]) -> ([a], Set a) -> Set a
iter _ ([], old) = old
iter f (t:ts, old) =
  let new = filter (not . (`Set.member` old)) $ f t old
   in iter f (ts <> new, old <> Set.singleton t)

applyRules rules ts = mconcat $ map (\r -> evalRule r ts) rules
iterRules rules = result
  where
    (start, rest) = partition emptyBody rules
    emptyBody (Rule (Closure _ Unit) _) = True
    emptyBody _ = False
    ts = applyRules start Set.empty
    f t old = mconcat $ map (\r -> step r t old) rest
    result = iter f (ts, Set.empty)

ce = Closure B.empty
var x = TermVar x

-- check :: E -> [Tuple] -> Maybe Tuple
check _ [] = Nothing
check e tts@(t : ts) =
  case check e ts of
    Nothing -> if not ok then Just (t, v1, v2) else Nothing
    Just x -> Just x
  where
    ok = Set.fromList v1 == Set.fromList v2
    v1 = eval (ce e) tts
    v2 = eval (ce e) ts <> do
      cl <- specialize (ce e) t
      v <- eval cl ts
      pure v

instance PP Term where
  pp (TermVar v) = v
  pp (TermPred p) = p
  pp (TermNum i) = show i
  pp (TermId i) = pp i
  pp TermBlank = "_"
  pp (TermApp cons ts) = cons <> args (map pp ts)
instance PP Id where
  pp (Id n vs) = n <> bwrap (unwords $ map pp vs)
