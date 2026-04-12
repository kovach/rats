module ConcatParse where

import Control.Monad ( guard, when, zipWithM_ )
import qualified Data.Map.Strict as Map
import Basic
import Data.Function ( on )
import Data.Monoid ( All(..), Any(..) )

import Prelude hiding ( Word )
import Control.Monad.Writer ( WriterT, runWriterT, tell, execWriter, Writer )
import Control.Monad ( foldM )
import Control.Monad.State

import Data.Function ((&))
import Data.List as List hiding ( insert )
import Data.Maybe hiding ( mapMaybe )
import Text.Read ( readMaybe )
import Data.Char
import Data.List.Split

type Pred = String
data Var = IVar String | GenVar String
  deriving (Eq, Ord, Show)

varStr :: Var -> String
varStr (IVar s)    = s
varStr (GenVar s) = s

data Word a
  = Atom Pred Int [Word a] [Word a] -- predicate, arity, leftmost args, rightmost args
  | Pair (Word a) (Word a) | Nil
  | Var Var | Skip | Term a
  deriving (Eq, Show)

-- Examples
-- require definition in Compile to run
tests' =
  [ "a a:b b:c c"
  , "a (a:b b)"
  , "p (I & q) r I"
  , "cat & black X"
  , "(cat&black&long) X"
  , "& a b c"
  , "a (b & c)"
  , "a (& b c)"
  , "a (:b B & c)"
  , "a (:b B & :c c)"
  , "a (*:b B & *:c c)" -- skip optional here
  , "a (:b b & :c c)"
  , "a (:b B & :c c/d d/e e)"
  , "q (p p:q)"
  , "f (A a:sum:b B)"
  , "the (long & black & cat) is at X"
  , "P p It it:range R"
  , "Q P p:q"
  ]

isLeaf  = \case
  Skip -> True; Var{} -> True; Nil -> True; Term{} -> True
  Atom{} -> False; Pair{} -> False

isVar = \case Var{} -> True; _ -> False

tr f = execWriter . go
  where
    go w = do
      tell (f w)
      case w of
        Pair l r       -> go l >> go r
        Atom _ _ ls rs -> mapM_ go (ls <> rs)
        _              -> pure ()

all f = getAll . tr (All . f)
any f = getAny . tr (Any . f)

-- variables in term
vars :: Word a -> [Var]
vars = tr $ \case Var v -> [v]; _ -> []

findAll :: (Word a -> Bool) -> Word a -> [Word a]
findAll p = tr $ \w -> [w | p w]

-- atoms with >0 arity are incomplete
completeWord :: Word a -> Bool
completeWord = ConcatParse.all check
  where
    check (Atom _ i _ _) | i > 0 = False
    check _ = True

-- All the operations are left/right biased depending on whether
-- they are acting the left or right half of an adjacent pair.
data Direction = R | L

-- Skip is used to shift the arguments to an atom; does not consume arity when bound
insert L Skip (Atom p n ls rs) = Atom p n (Skip : ls) rs
insert L x  (Atom p n ls rs)   = Atom p (n-1) (x : ls) rs
insert R Skip (Atom p n ls rs) = Atom p n ls (Skip : rs)
insert R x  (Atom p n ls rs)   = Atom p (n-1) ls (x : rs)
insert _ _ _ = error ""

isTerm _ v@Skip  = Just (Nil, v)
isTerm _ v@Var{} = Just (Nil, v)
isTerm _ Term{} = Nothing
isTerm R (Pair l r) | Just (r', t) <- isTerm R r = Just (pair l r', t)
isTerm R (Pair l r) | Just (l', t) <- isTerm R l = Just (pair l' r, t)
isTerm L (Pair l r) | Just (l', t) <- isTerm L l = Just (pair l' r, t)
isTerm L (Pair l r) | Just (r', t) <- isTerm L r = Just (pair l r', t)
isTerm _ _ = Nothing

pattern BinOp2 op = Term op
pattern BinOp1 x op = Pair x (BinOp2 op)
pattern BinOp0 x op y  = Pair (BinOp1 x op) y

-- Monad for accessing a supply of fresh names
data Stream a = Stream a (Stream a)
freshVars :: Stream String
freshVars = go 1
  where
    go n = Stream ("X" <> show n) (go (n+1))

type M b = State (Stream String) b
fresh :: M String
fresh = do
  Stream h t <- get
  put t
  pure h
runM s = evalState s freshVars

slot R (Pair l r) | Just k <- slot R r = Just (Pair l . k)
slot R (Pair l r) | Just k <- slot R l = Just (flip Pair r . k)
slot L (Pair l r) | Just k <- slot L l = Just (flip Pair r . k)
slot L (Pair l r) | Just k <- slot L r = Just (Pair l . k)
slot d x@(Atom _ i _ _) | i > 0 = Just $ \v -> insert d v x
slot _ _ = Nothing

join :: Word a -> Word a -> M (Word a)
Nil `join` x = pure x
x `join` Nil = pure x
-- TODO?: force complete term for BinOp0?
x `join` BinOp2 op = pure $ BinOp1 x op
BinOp1 x op `join` y = pure $ BinOp0 x op y
-- connect a term and a slot
u `join` v | Just (v', t) <- isTerm L v, Just kr <- slot R u = join (kr t) v'
v `join` u | Just (v', t) <- isTerm R v, Just kl <- slot L u = join v' (kl t)
-- generate a fresh var, join two slots
u `join` v | Just kl <- slot R u
           , Just kr <- slot L v = do
  x <- Var . GenVar <$> fresh
  pure $ Pair (kl x) (kr x)
x `join` y = pure $ Pair x y

simpl (Pair l r) = Pair (simpl l) (simpl r)
simpl (Atom p i ls rs) = Atom p i (fix ls) (fix rs)
  where
    fix (Skip : vs) = rotateR $ fix vs
    fix (v : vs) = v : fix vs
    fix [] =[]
    rotateR (h : t) = t <> [h]
    rotateR [] = []

simpl x = x

-- probably this control flow can be cleaned up
solve :: Word a -> M (Word a)
solve (Pair l r) = do { l' <- solve l; r' <- solve r; join l' r' }
solve (Atom p i l r) = do
  l' <- mapM solve l
  r' <- mapM solve r
  pure $ Atom p i l' r'
solve x = pure x
runSolve = runM . solve

pair Nil x = x
pair x Nil = x
pair x y = Pair x y

oneWord :: [Word a] -> Word a
oneWord = foldl' pair Nil

newJoin :: [Word a] -> Word a
newJoin = simpl . runSolve . oneWord

instance PP Var where
  pp (IVar v) = "_" <> v
  pp (GenVar v) = v
instance PP a => PP (Word a) where
  pp (Pair l r) = pp l <> " " <> pp r
  pp (Atom p i ls rs) = (if i > 0 then "[!"<>show i<>"]" else "") <> pwrap (unwords (p : map pp (reverse ls <> rs)))
  pp (Var v) = pp v
  pp (Skip) = "*"
  pp (Term a) = pp a
  pp Nil = "."

data Token = Token String deriving (Eq, Ord, Show)

pickToken :: (String -> Maybe (Token, String)) -> String -> [Token]
pickToken sp = pickToken' ""
  where
    pickToken' acc ""                      = token acc
    pickToken' acc s | Just (t, s') <- sp s = (token acc) <> [t] <> pickToken' "" s'
    pickToken' acc (c:s') | isSpace c       = token acc <> pickToken' "" s'
    pickToken' acc (c:s')                   = pickToken' (c:acc) s'
    token "" = []
    token acc = [Token $ reverse acc]


tokenize :: (String -> Maybe (Token, String)) -> String -> [Token]
tokenize sp s = pickToken sp s

fx :: PP a => [String] -> (Token -> Maybe (Word a)) -> String -> [Word a]
fx specialTokens turnWord =
    tokenize peel
    .> splitRules
    .> map (check . newJoin . go)
  where
    check x = if not (completeWord x) then error ("incomplete: " <> pp x) else x
    peel (x:r) = if [x] `elem` specialTokens' then Just (Token [x], r) else Nothing
    peel _ = error "unreachable"
    internalSpecialTokens = ["(", ")", "*"]
    specialTokens' = internalSpecialTokens <> specialTokens
    go ts = finishWord $ foldl' step [[]] ts
    finishWord = \case
      [ws] -> reverse ws
      _ -> error "mismatched parens"
    step stack (Token "(" ) = [] : stack
    step [_] (Token ")") = error "unmatched ')'"
    step (ws : stacks) (Token ")") = push (oneWord $ reverse ws) stacks
    step stacks x  = push (single x) stacks
    push x (s : rest) = (x:s):rest
    push _ _ = error "unreachable"
    single t | Just w <- turnWord t      = w
    single (Token s@(x : _)) | isUpper x = Var (IVar s)
    single (Token s@('_' : _))           = Var (IVar s)
    single (Token "*")                   = Skip
    single (Token [])                    = error "empty word"
    single (Token p)                     = error $ "invalid word: " <> p
    splitRules :: [Token] -> [[Token]]
    splitRules = filter (not . null) . splitOn [Token "."]

mapMaybe :: (Word a -> Maybe (Word a)) -> Word a -> Word a
mapMaybe f w = fromMaybe w' (f w')
  where
    go = mapMaybe f
    w' = case w of
      Pair l r       -> pair (go l) (go r)
      Atom p n ls rs -> Atom p n (map go ls) (map go rs)
      _              -> w

applySubst :: Map.Map Var (Word a) -> Word a -> Word a
applySubst s = mapMaybe $ \case
  Var v -> Map.lookup v s
  _     -> Nothing

mergePred :: Eq a => Pred -> Word a -> Word a
mergePred p w =
  case targets of
    t : _ -> mergePred p $ elim t
    _ -> w
  where
    targets = findAll isTarget w

    isTarget (Atom p' 0 ls rs) | p' == p = List.all isVar (ls <> rs)
    isTarget _                           = False

    elim t = applySubst (mkSubst t) $
      mapMaybe (\x -> if x == t then Just Nil else Nothing) w

    mkSubst (Atom _ 0 ls rs) = result
      where
        vs = [v | Var v <- ls <> rs]
        canon = case filter isIVar vs of { c:_ -> c; [] -> head vs }
        isIVar = \case (IVar _) -> True; _ -> False
        result = case vs of
           [] -> Map.empty
           _  -> Map.fromList [(r, Var canon) | r <- vs, r /= canon]
    mkSubst _ = Map.empty

-- IVar and GenVar are treated equivalently
alphaEquiv :: Eq a => Word a -> Word a -> Bool
alphaEquiv w1 w2 = isJust $ execStateT (go w1 w2) (Map.empty, Map.empty)
  where
    go (Var v1) (Var v2) = do
      (fwd, bwd) <- get
      case (Map.lookup v1 fwd, Map.lookup v2 bwd) of
        (Just v2', Just v1') -> guard (v2' == v2 && v1' == v1)
        (Nothing,  Nothing)  -> put (Map.insert v1 v2 fwd, Map.insert v2 v1 bwd)
        _                    -> guard False
    go (Atom p1 n1 ls1 rs1) (Atom p2 n2 ls2 rs2) = do
      guard (p1 == p2 && n1 == n2 && length ls1 == length ls2 && length rs1 == length rs2)
      zipWithM_ go ls1 ls2
      zipWithM_ go rs1 rs2
    go (Pair l1 r1) (Pair l2 r2) = go l1 l2 >> go r1 r2
    go Nil         Nil           = pure ()
    go Skip        Skip          = pure ()
    go (Term a1)   (Term a2)     = guard (a1 == a2)
    go _           _             = guard False


-- tests
