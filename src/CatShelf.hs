module CatShelf where

import Prelude hiding (Word, lex)
import Control.Monad.State
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Control.Monad.Except
import Data.Char
import Data.Function ((&))
import Data.List
import Data.Maybe
import Data.String
import Text.Read (readMaybe)

type Pred = String
type Var = String
type Sym = String
data Literal = LitInt Int | LitSym Sym
pwrap x = "(" <> x <> ")"

data Ty = Ty String
  deriving (Eq, Show, Ord)
--data Tuple = Tuple String [Literal]
type Arity = [Ty]
type Schema = Pred -> [Arity]
data Term a = Term a | TermVar Var | TermPred Pred
  deriving (Eq, Show, Ord)
data Atom a = Atom Pred [Term a]
  deriving (Eq, Ord, Show)
--instance Show a => Show (Atom a) where
--  show (Atom p ts) = "atom@(" <> show p <> " " <> unwords (map show ts) <> ")"
data Word a = WTerm (Term a) | WPred Pred | WPush | WPop | WHole
  deriving (Eq, Show, Ord)

data Temp a
  -- a partially applied atom with `Arity` missing arguments.
  = TempAtom [Term a] Arity Ty
  | TempHole
  | Temps [Temp a]
  | TempPush | TempPop
  deriving (Eq)

instance IsString (Term a) where
  fromString = TermPred

-- lexicon
_t = Ty "term"
_te = Ty "turn-expr"
_join op = TempAtom [op] [_te, _te] _te
_comma = _join ","
_var v = TempAtom [v] [] _t

predArity :: String -> Arity
predArity = (flip replicate _t) . (+1) . length . filter (== '/')

holeSymbol = "."
hole = TermVar holeSymbol

split delim s = (takeWhile (/= delim) s, drop 1 $ dropWhile (/= delim) s)

parseLit s =
  case readMaybe s of
    Just i -> LitInt i
    _ -> LitSym s

sh :: Show a => [a] -> String
sh = unwords . map show

instance Show a => Show (Temp a) where
  -- show (TempTerm v) = show v
  show (TempHole) = holeSymbol
  show (TempAtom vs ar a) = pwrap $ (sh vs) <> "/" <> (sh ar) <> ":" <> show a
  show (Temps ts) = "[" <> intercalate " | " (map show ts) <> "]"
  show TempPush = "push"
  show TempPop = "pop"

type M b a = ExceptT String (WriterT [Atom b] (StateT Int [])) a

fresh' :: (MonadState Int m) => m Var
fresh' = do
  s <- get
  modify (+1)
  pure $ show s

fresh :: (MonadState Int m) => String -> m Var
fresh str = do
  v <- fresh'
  pure $ str <> v

-- reverse, but also deal with holes
-- each hole rotates the topmost parameter to the end
fixVars :: Eq a => [Term a] -> [Term a]
fixVars x = fix x'
  where
    x' = reverse x

    -- this is not obviously correct (or is it incorrect?)
    fix [] = []
    fix (h : vs) | h == hole = rotate (fix vs)
    fix (v : vs) = v : fix vs

    rotate [] = []
    rotate z = last z : init z

type Stack a = [a]

-- Parse state. left side: progress, right side: input sentence.
type St a = (Stack (Temp a), Stack (Temp a))
data St' a = StNil { stVal :: St a } | St { stVal :: St a, stTail :: (St' a) }
  deriving (Eq, Show)

class OfTempAtom a where
  finish :: [Term a] -> Ty -> a

step :: (OfTempAtom a, Eq a, Show a) => St a -> M a (St a)

-- [nondeterminism in lexicon]
--   We handle words that have multiple possible arities here.
step (l, Temps ts : r) = do
  t <- lift $ lift $ lift $ ts
  pure (l, t : r)

-- Introduce join
step (lt@(TempAtom _ [ty] _ : _), rt@(TempAtom _ (ty':_) _ : _)) | ty == ty' =
  do
    v <- TermVar <$> fresh'
    pure (lt, _var v : _comma : _var v : rt)
-- swap and apply the first case
step (x1@(TempAtom _ (ty':_) _) : l, x2@(TempAtom _ [ty] _) : r) | ty == ty' = pure (x2 : l, x1 : r)

-- Apply to term
step ((TempAtom args [] ty : l), (TempAtom bound (ty':minusOne) outTy : r)) | ty == ty' =
  pure (l, TempAtom (bound <> [Term $ finish args ty]) minusOne outTy : r)
step (x1@(TempAtom _ (ty':_) _) : l,  x2@(TempAtom _ [] ty) : r) | ty == ty' =
  step (x2 : l, x1 : r)

--step (TempAtom p vs a : l,  TempHole : r) =
--  pure (l, TempAtom p (hole : vs) a : r)
--step (TempHole : l, TempAtom p vs a : r) =
--  pure (l, TempAtom p (hole : vs) a : r)

-- [paren handling]
step (l, TempPush : r) = pure (TempPush : l, r)
step (x : TempPush : l, TempPop : r) = pure (l, x : r)
step s@(_, TempPop : _) = throwError $ "mismatched ')':\n" <> show s

-- [push step]
--   Otherwise, push the next word to the stack
step (l, w@(TempAtom {}) : r) = pure (w : l, r)
step (l, w@(TempHole {}) : r) = pure (w : l, r)

-- [done]
step (s, []) = pure (s, [])

step' st = do
  a' <- step (stVal st)
  pure $ St a' st


wrap :: (Eq a, Monad m) => (a -> m a) -> a -> m (Maybe a)
wrap f x = do
  x' <- f x
  pure $ if x == x' then Nothing else Just x'

data ParseResult a b
  = Error String [Atom a]
  | Success0 [Atom a]
  | Success1 [Atom a] b
  deriving (Show)

defaultSchema :: Schema
defaultSchema = \s -> [predArity s]

run1'' :: (Eq a, Show a, OfTempAtom a) => [Temp a] -> [Either String [St' a]]
run1'' ws = map (fst . fst) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
    out <- iter' 80 (wrap step') (StNil ([], ws))
    pure out

run1' :: (Eq a, Show a, OfTempAtom a) => [Temp a] -> [Either String [St a]]
run1' ws = map (fst . fst) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
    out <- iter' 80 (wrap step) ([], ws)
    pure out

run1 :: (Eq a, Show a, OfTempAtom a) => [Temp a] -> [ParseResult a a]
run1 ws = map (check) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
    out <- iter (wrap step) ([], ws)
    let out' = last out
    case out' of
      ([], []) -> pure Nothing
      --([t], []) -> pure $ Just t
      ([TempAtom args [] ty], []) -> pure $ Just $ finish args ty
      _ -> throwError $ "bad parse. temp term remaining: " <> show out'
  where
    check ((Left err, atoms), _) = Error err atoms
    check ((Right Nothing, atoms), _) = Success0 atoms
    check ((Right (Just t), atoms), _) = Success1 atoms t

iter' :: Monad m => Int -> (a -> m (Maybe a)) -> a -> m [a]
iter' 0 _ v = pure [v]
iter' n f v = do
  v' <- f v
  case v' of
    Nothing -> pure [v]
    Just v'' -> do
      r <- iter' (n-1) f v''
      pure (v : r)

iter :: Monad m => (a -> m (Maybe a)) -> a -> m [a]
iter f v = do
  v' <- f v
  case v' of
    Nothing -> pure [v]
    Just v'' -> do
      r <- iter f v''
      pure (v : r)

run2 :: String -> [ParseResult E E]
run2 = run1 . map (tokenize defaultSchema) . lex

runCatShelf base = do
  f <- readFile (base <> ".turn")
  case run2 f of
    Success1 _ t : _ -> print t
    Error str _ : _ -> putStrLn str
    _ -> error "todo"

data JoinOp = Binary String String | Fixed String
  deriving (Eq, Show)

data E
  = Leaf [E] -- e's must be t's
  | Join JoinOp E E
  | TVar Var
  | TPred Pred
  deriving (Eq, Show)

specialTokens =
  [ "("
  , ")"
  , "<="
  , ","
  , "~" ]
endpointMarkers :: [Char]
endpointMarkers = "~=<>"
isEndpointJoin a b = a `elem` endpointMarkers && b `elem` endpointMarkers
toJoinOp :: String -> Maybe JoinOp
toJoinOp = \case
  "," -> Just $ Fixed ","
  "~" -> Just $ Fixed "~"
  [a,b] | isEndpointJoin a b -> Just $ Binary [a] [b]
  _ -> Nothing

efix (TermVar v) = TVar v
efix (TermPred p) = TPred p
efix (Term t) = t

instance OfTempAtom E where
  finish [TermPred pr, (Term x), (Term y)] ty | ty == _te, Just op <- toJoinOp pr = Join op x y
  finish (TermPred p : ts) ty | ty == _te = Leaf (TPred p : map efix ts)
  finish [TermVar v] ty | ty == _t = TVar v
  finish ts _ = error $ show ts

data Token = Token String
  deriving (Eq, Ord, Show)
startSpecial :: String -> Maybe (Token, String)
startSpecial (a:b:r) | isEndpointJoin a b = Just (Token [a,b], r)
startSpecial s | Just r <-
    case mapMaybe (\t -> stripPrefix t s >>= \s' -> pure (t, s')) specialTokens of
      [(t,s')] -> Just (Token t, s')
      _ -> Nothing
  = Just r
startSpecial _ = Nothing
token "" = []
token acc = [Token $ reverse acc]
pickToken' acc "" = token acc
pickToken' acc s | Just (t, s') <- startSpecial s = (token acc) <> [t] <> pickToken' "" s'
pickToken' acc (c:s') | isSpace c = token acc <> pickToken' "" s'
pickToken' acc (c:s') = pickToken' (c:acc) s'
pickToken s = pickToken' "" s
pickOne "" = Nothing
pickOne s = let (t, r) = break isSpace s in Just (Token t, drop 1 r)
lex s = pickToken s

tokenize :: Schema -> Token -> Temp a
tokenize _s (Token "(") = TempPush
tokenize _s (Token ")") = TempPop
tokenize _s (Token "_") = TempHole
tokenize _s (Token pr) | Just _ <- toJoinOp pr = _join $ TermPred pr
tokenize _s (Token s@(x : _)) | isUpper x = _var $ TermVar s
tokenize _s (Token s@('_' : _))           = _var $ TermVar s
tokenize  s (Token p@(_ : _)) = Temps [ TempAtom [TermPred p] ar _te | ar <- s p ]
tokenize _s (Token []) = error "empty word"

eg1 = "cat on shelf"
eg1' = "on cat shelf"
eg2 = "cat on shelf shelf on cat"
eg3 = "cat sees cat with telescope" -- surprising?
eg5 = "cat cat cat cat"
eg6 = "cat X X on Y"
eg6' = "cat ?x ?x on Y"
eg7 = "X cat on X Y"

bad1 = "cat on" -- bad, incomplete
bad2 = "on on" -- bad, incomplete

-- confusing examples
conf1  = "on on cat cat"  -- a cat is on something that is on a cat
conf1' = "on cat on cat" -- a cat is on something that is on a cat
conf2  = "X Y on" -- Y is on X

chk x =
  case run2 x of
    [Error e _] -> putStrLn e
    v -> print v
tests =
  []
  -- [eg1, eg1', eg2, eg3, eg5, eg6, eg6', eg7, bad1, bad2, conf1, conf1', conf2]
  <> ["(cat on) cat"]

printParseResult (Error e _) = putStrLn $ e <> "\n"
printParseResult (Success0 q) = putStrLn $ unlines (map show q)
printParseResult (Success1 q t) = putStrLn $ show t <> "\n" <> unlines (map show q)
