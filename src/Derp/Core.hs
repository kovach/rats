-- "DERiving Predicates"
module Derp.Core (module Derp.Core, module Derp.Types) where

import Data.Maybe
import Control.Monad hiding (join)
import Data.List hiding (take)
import Prelude hiding (take)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Writer
import Debug.Trace

import Basic
import qualified Binding as B
import qualified MMap
import Derp.Types

immediate = \case
  Unit -> True
  Bind {} -> True
  Join a b -> immediate a && immediate b
  Atom {} -> False
  NegAtom {} -> False

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

merge (Binding b1 d1) (Binding b2 d2) = do
  b' <- B.merge b1 b2
  pure (Binding b' (d1 <> d2))

-- todo instance Collection Binding where
single k v = Binding (B.ofList [(k,v)]) mempty

specialize :: CE -> Tuple -> [CE]
specialize (Closure _ Unit) _ = []
specialize (Closure _ Bind{}) _ = []
specialize (Closure _ NegAtom{}) _ = []
specialize (Closure b (Atom pat)) tuple = do
  b' <- maybeToList $ B.unify b pat tuple
  pure $ Closure b' Unit
-- d(a b) = d(a) b + a d(b) + d(a) d(b)
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
evalBuiltin _ op as = error $ "unimplemented: " <> op <> args (map pp as)

eval :: CE -> Tuples -> Tuples -> [Binding]
eval (Closure b Unit) _ _ = [b]
eval (Closure b (Bind x y)) _ _ = maybeToList $ B.unify b x (subTerm (bind b) y)
eval (Closure b (SpecialAtom p ts)) _ _ = evalBuiltin b p ts
eval (Closure c (Atom (TermPred p : vs))) (Tuples tuples) _ =
  concatMap (map context . specialize (Closure c (Atom vs))) (MMap.lookup p tuples)
eval (Closure _ (Atom _)) _ _ = error "todo"
eval (Closure b@(Binding bs _) (NegAtom at)) _ check =
  if subst bs at `member` check then [] else [b]
eval (Closure c (Join a b)) tuples check = do
  c' <- eval (Closure c a) tuples check
  c'' <- eval (Closure c' b) tuples check
  pure c''

eval1 :: CE -> Tuple -> Tuples -> Tuples -> [Binding]
eval1 cl t ts check = do
  cl' <- specialize cl t
  v <- eval cl' ts check
  pure v

subTerm ctx = \case
    TermVar n ->
      case B.lookup n ctx of
        Just v -> v
        Nothing -> error $
          unlines ["[variable binding]", show ctx, n]
    TermApp cons ts -> TermApp cons (map (subTerm ctx) ts)
    TermBlank -> error ""
    x -> x

subst :: B.Binding Name Term -> Tuple -> Tuple
subst ctx tuple = map (subTerm ctx) tuple

substs :: B.Binding Name Term -> [Tuple] -> [Tuple]
substs ctx = map (subst ctx)

toThunk :: [Tuple] -> Binding -> [Thunk]
toThunk hd (Binding ctx ns) = [ Thunk (substs ctx hd) (substs ctx ns) ]

stepRule :: Rule -> Tuple -> Tuples -> Tuples -> [Thunk]
stepRule (Rule body hd) t ts check = do
  b <- eval1 body t ts check
  toThunk hd b

evalRule (Rule body hd) ts check = do
  b <- eval body ts check
  toThunk hd b

partitionThunks :: [Thunk] -> ([Thunk], [Thunk])
partitionThunks = partition (\case Thunk _ deps -> size deps > 0)

takeThunk (Thunk hd []) = Set.fromList hd
takeThunk _ = error ""
evalThunk db (Thunk hd deps) =
  if any (`member` db) deps then mempty else Set.fromList hd
evalThunks db ts = mconcatMap (evalThunk db) ts

-- f : program
-- ts : worklist
-- changed : new tuples \ (ts, base)
-- db : entire fixpoint
-- check : previous fixpoint, used to evaluate negation
iter :: (Tuple -> Tuples -> Tuples -> [Thunk]) -> Set Tuple -> (Set Tuple, Tuples) -> Tuples -> Tuples -> (Tuples, Set Tuple)
iter f ts (changed, base) db check =
  case pick ts of
    Nothing -> (db, changed)
    Just (t, ts') -> iter f ts'' (changed', base) db' check
      where
        new_ = f t db check
        tuples = mconcatMap takeThunk new_
        new = Set.filter (not . (`member` db)) tuples
        changed' = changed <> Set.filter (not . (`member` base)) new -- accum values for debugging only
        ts'' = ts' <> new
        db' = db <> one t

tracen False _ a = a
tracen True m a = trace m a

-- Alternating fixpoint
altIter 0 _ _ _ = error "gas"
altIter n ts0 f v = trace ("STEP: " <> show n) $ out
  where
    (v1, gen1) = iter f ts0 (none, v) mempty v
    (v2, gen2) = iter f ts0 (none, v) mempty v1
    out = tracen dbg dbgMsg $
      if isEmpty gen1 then v1 -- happens when program has no unfounded atoms
      else if isEmpty gen2 then v2
      else altIter (n-1) ts0 f v2

    dbg = False
    dbgMsg = ("g1: " <> show gen1 <> "\n") <> ("g2: " <> show gen2 <> "\n")

applyRules :: [Rule] -> Tuples -> Set Tuple
applyRules rules ts = mconcatMap takeThunk $ mconcat $ map (\r -> evalRule r ts mempty) rules

iterRules allRules = result
  where
    (start, rest) = partition unitBody allRules
    -- (negative, positive) = partition hasNegation rest
    unitBody (Rule (Closure _ e) _) = immediate e
    -- hasNegation (Rule (Closure _ e) _) = length (findNegations e) > 0
    ts0 = applyRules start mempty
    f :: [Rule] -> Tuple -> Tuples -> Tuples -> [Thunk]
    f rules t old check = mconcat $ map (\r -> stepRule r t old check) rules
    result = altIter 10 ts0 (f rest) mempty

-- ce = Closure mempty
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
