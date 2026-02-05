-- "DERiving Predicates"
module Derp where

import Data.Maybe
import Control.Monad hiding (join)
import Data.List hiding (take)
import Prelude hiding (take)
import Data.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Writer
import Debug.Trace

import Basic
import qualified Binding as B
import qualified MMap

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
  | TermString String
  deriving (Show, Eq, Ord)

data E
  = Atom Tuple
  | NegAtom Tuple
  | Bind Term Term
  | Join E E
  | Unit
  deriving (Show, Eq, Ord)

immediate = \case
  Unit -> True
  Bind {} -> True
  Join a b -> immediate a && immediate b
  Atom {} -> False
  NegAtom {} -> False

pattern SpecialAtom p ts = Atom (TermPred ('#' : p) : ts)

join Unit x = x
join x Unit = x
join x y = Join x y

atom [] = Unit
atom t = Atom t

simplify = \case
  Join a b -> join (simplify a) (simplify b)
  Atom at -> atom at
  x -> x

joins :: Foldable f => f Tuple -> E
joins = foldr (\x acc -> join (atom x) acc) Unit
joins' :: Foldable f => f E -> E
joins' = foldr (\x acc -> join x acc) Unit

eTraverse :: Applicative m => (E -> m E) -> E -> m E
eTraverse f = go
  where
    go e@(Atom _) = f e
    go e@(NegAtom _) = f e
    go e@Unit = f e
    go e@(Bind _ _) = f e
    go (Join a b) = Join <$> (go a) <*> (go b)

eTraverse' :: Applicative m => (E -> m ()) -> E -> m ()
eTraverse' f e0 = eTraverse (\e -> f e *> pure e) e0 *> pure ()

findNegations = execWriter . eTraverse' go
  where
    go (NegAtom t) = tell [t]
    go _ = pure ()

type Neg = Map Tuple [Tuple]
data Binding = Binding { bind :: B.Binding Name Term, bdeps :: [Tuple] }
  deriving (Show, Eq, Ord)

data Thunk = Thunk { tuples :: [Tuple], deps :: [Tuple] }
  deriving (Show, Eq, Ord)

instance Semigroup Binding where
  (Binding b1 d1) <> (Binding b2 d2) = Binding (b1 <> b2) (d1 <> d2)

empty = Binding mempty none

instance Monoid Binding where
  mempty = empty

merge (Binding b1 d1) (Binding b2 d2) = do
  b' <- B.merge b1 b2
  pure (Binding b' (d1 <> d2))

-- todo instance Collection Binding where
single k v = Binding (B.ofList [(k,v)]) mempty

data Closure a = Closure { context :: Binding, clVal :: a }
  deriving (Show, Eq, Ord, Functor)
type CE = Closure E

data Rule = Rule { body :: CE, head :: [Tuple] }
  deriving (Show, Eq, Ord)

instance B.Unify Binding Term Term where
  unify b TermBlank _ = pure b
  unify b _ TermBlank = pure b
  unify (Binding b d) (TermVar var) v  = (\b' -> (Binding b' d)) <$> (B.unify b var v)
  unify b l@(TermPred _) r = guard (l == r) >> pure b
  unify b l@(TermNum _) r  = guard (l == r) >> pure b
  unify b l@(TermId _) r   = guard (l == r) >> pure b
  unify b l@(TermString _) r   = guard (l == r) >> pure b
  unify b (TermApp cons ts) (TermApp cons' ts') = do
    guard $ cons == cons'
    B.unify b ts ts'
  unify _ (TermApp {}) _ = fail "app"

instance B.Unify Binding [Term] [Term] where
  unify b x y = do
      go b x y
    where
      go c (t:ts) (v:vs) = do
        c' <- (B.unify c t v)
        go c' ts vs
      go c [] [] = pure c
      go _ _ _ = Nothing

type Tuple = [Term]
specialize :: CE -> Tuple -> [CE]
specialize e@(Closure _ Unit) _ = [e]
specialize (Closure _ Bind{}) _ = []
specialize (Closure _ NegAtom{}) _ = []
specialize (Closure b (Atom pat)) tuple = do
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

evalBuiltin b "range" [_, t, TermNum lo, TermNum hi] = do
  i <- [lo..hi]
  case B.unify b t (TermNum i) of
    Just b' -> pure b'
    _ -> []
-- evalBuiltin b "eq" [x, y] = maybeToList $ B.unify b x y
evalBuiltin _ op as = error $ "unimplemented: " <> op <> args (map pp as)

newtype Tuples = Tuples (MMap.MMap Pred (Set Tuple))
  deriving (Semigroup, Monoid)

instance Collection' Tuples where
  size (Tuples m) = sum $ map (\(_, vs) -> size vs) $ MMap.toList m
instance Collection Tuple Tuples where
  one (TermPred p : vs) = Tuples (MMap.singleton p (one vs))
  one _ = error ""
  member (TermPred p : vs) (Tuples m) = vs `member` MMap.lookup p m
  member _ _ = error ""
instance PP Tuples where
  pp (Tuples m) = out
    where
      fix (k, vs) = map (TermPred k:) $ Set.toList vs
      tuples = mconcat $ map fix $ MMap.toList m
      out = unlines . map pp $ tuples

eval :: CE -> Tuples -> [Binding]
eval (Closure b Unit) _ = [b]
eval (Closure b (Bind x y)) _ = maybeToList $ B.unify b x y
eval (Closure b (SpecialAtom p ts)) _ = evalBuiltin b p ts
eval (Closure c (Atom (TermPred p : vs))) (Tuples tuples) =
  concatMap (map context . specialize (Closure c (Atom vs))) (MMap.lookup p tuples)
eval c@(Closure _ (Atom _)) tuples = error "todo"
eval (Closure (Binding bs as) (NegAtom at)) _ = [Binding bs (as <> [at])]
eval (Closure c (Join a b)) tuples = do
  c' <- eval (Closure c a) tuples
  c'' <- eval (Closure c' b) tuples
  pure c''

eval1 :: CE -> Tuple -> Tuples -> [Binding]
eval1 cl t ts = do
  cl' <- specialize cl t
  v <- eval cl' ts
  pure v

subTerm ctx = \case
    TermVar n -> fromJust $ B.lookup n ctx
    TermApp cons ts -> TermApp cons (map (subTerm ctx) ts)
    TermBlank -> error ""
    x -> x

subst :: B.Binding Name Term -> Tuple -> Tuple
subst ctx tuple = map sub1 tuple
  where
    sub1 (TermVar n) = fromJust $ B.lookup n ctx
    sub1 (TermApp cons ts) = TermApp cons (map sub1 ts)
    sub1 TermBlank = error ""
    sub1 x = x

substs :: B.Binding Name Term -> [Tuple] -> [Tuple]
substs ctx = map (subst ctx)

toThunk :: [Tuple] -> Binding -> [Thunk]
toThunk hd (Binding ctx ns) = [ Thunk (substs ctx hd) (substs ctx ns) ]

step :: Rule -> Tuple -> Tuples -> [Thunk]
step (Rule body hd) t ts = do
  b <- eval1 body t ts
  toThunk hd b

evalRule :: Rule -> Tuples -> [Thunk]
evalRule (Rule body hd) ts = do
  b <- eval body ts
  toThunk hd b

-- anyVal _ [] = Nothing
-- anyVal map (k:ks) =
--   case Map.lookup k map of
--     Just v -> Just (k,v)
--     Nothing -> anyVal map ks

partitionThunks :: [Thunk] -> ([Thunk], [Thunk])
partitionThunks = partition (\case Thunk _ deps -> size deps > 0)

mconcatMap f = mconcat . map f
takeThunk (Thunk hd []) = Set.fromList hd
takeThunk _ = error ""
evalThunk db (Thunk hd deps) =
  if any (`member` db) deps then mempty else Set.fromList hd
evalThunks db ts = mconcatMap (evalThunk db) ts

iter f (ts, thunks, db) =
  case take ts of
    Nothing ->
      if size thunks > 0
         then -- todo
           let new_ = evalThunks db thunks
            in iter f (new_, none, db)
         else db
    Just (t, ts') -> st
      where
        hs = f t db
        (blocked, new_) = partitionThunks hs
        tuples = mconcatMap takeThunk new_
        new = Set.filter (not . (`member` db)) tuples
        st = iter f (ts' <> new, thunks <> blocked, db <> one t)

--iterStrata ts fs = iterStrata' fs (ts, mempty, ofList ts) fs
--iterStrata' f0 (_, delta, old) [] = if Set.size delta == 0 then old else iterStrata (Set.toList old) f0
--iterStrata' f0 (ts, delta, old) (f:fs) =
--  let (delta', old') = iter f (ts, delta, old)
--   in iterStrata' f0 (Set.toList old', delta', old') fs

applyRules :: [Rule] -> Tuples -> Set Tuple
applyRules rules ts = mconcatMap takeThunk $ mconcat $ map (\r -> evalRule r ts) rules

iterRules allRules = result
  where
    (start, rest) = partition unitBody allRules
    -- (negative, positive) = partition hasNegation rest
    unitBody (Rule (Closure _ e) _) = immediate e
    unitBody _ = False
    hasNegation (Rule (Closure _ e) _) = length (findNegations e) > 0
    ts0 = applyRules start mempty
    f rules t old = mconcat $ map (\r -> step r t old) rules
    -- fs = (map f [positive, negative])
    result = iter (f rest) (ts0, mempty, mempty)

ce = Closure mempty

--todo
--check :: E -> [Tuple] -> Maybe Tuple
--check _ [] = Nothing
--check e tts@(t : ts) =
--  case check e ts of
--    Nothing -> if not ok then Just (t, v1, v2) else Nothing
--    Just x -> Just x
--  where
--    ok = Set.fromList v1 == Set.fromList v2
--    v1 = eval (ce e) tts
--    v2 = eval (ce e) ts <> do
--      cl <- specialize (ce e) t
--      v <- eval cl ts
--      pure v

instance PP Term where
  pp (TermVar v) = v
  pp (TermPred p) = p
  pp (TermNum i) = show i
  pp (TermId i) = pp i
  pp TermBlank = "_"
  pp (TermApp cons ts) = cons <> args (map pp ts)
  pp (TermString s) = show s

instance PP Id where
  pp (Id n vs) = n <> bwrap (unwords $ map pp vs)
