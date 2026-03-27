-- Possible alternate names for this:
--    OOOPS = out-of-order predicate syntax
--    FLOPS = flexible-order ...
--    cat shelf = "cat on shelf"
module CatShelf where

-- High level idea:
-- logical form: cat(X)
-- natural sentential form: X (is) cat
--
-- "a cat is on a shelf"
-- cat(X), shelf(Y), on(X,Y)
-- (a) cat (is) on (a) shelf
-- insert (Var , Var) in between any pair where one is unary:
--   (a) cat [X , X] (is) on [Y , Y] (a) shelf
-- remove signaling words:
--   cat X, X on Y, Y shelf
-- standard form:
--   cat X, on X Y, shelf Y

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
type Arity = [Ty]
type Schema = Pred -> [Arity]
data Term a = Term a
  deriving (Eq, Show, Ord)
data Atom a = Atom Pred [Term a]
  deriving (Eq, Ord, Show)
--instance Show a => Show (Atom a) where
--  show (Atom p ts) = "atom@(" <> show p <> " " <> unwords (map show ts) <> ")"
data Word a = WTerm (Term a) | WPred Pred | WPush | WPop | WHole
  deriving (Eq, Show, Ord)

-- Item?
data Item a
  -- a partially applied atom with `Arity` missing arguments.
  = ItemAtom (Stack (Item a)) [Term a] Arity Ty
  | ItemHole
  | Items [Item a]
  | ItemPush | ItemPop
  deriving (Eq)

instance OfItem a => IsString (Term a) where
  fromString = Term . mkPred

-- lexicon
_t = Ty "term"
_te = Ty "turn-expr"
_join op = ItemAtom [] [Term op] [_te, _te] _te
_comma :: OfItem a => Item a
_comma = _join (mkPred ",")
_var v = ItemAtom [] [Term v] [] _t

predArity :: String -> Arity
predArity = (flip replicate _t) . (+1) . length . filter (== '/')

holeSymbol = "."
hole :: OfItem a => a
hole = mkVar holeSymbol

split delim s = (takeWhile (/= delim) s, drop 1 $ dropWhile (/= delim) s)

parseLit s =
  case readMaybe s of
    Just i -> LitInt i
    _ -> LitSym s

sh :: Show a => [a] -> String
sh = unwords . map show

instance Show a => Show (Item a) where
  -- show (ItemTerm v) = show v
  show (ItemHole) = holeSymbol
  show (ItemAtom _todo vs ar a) = pwrap $ (sh vs) <> "/" <> (sh ar) <> ":" <> show a
  show (Items ts) = "[" <> intercalate " | " (map show ts) <> "]"
  show ItemPush = "push"
  show ItemPop = "pop"

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
-- fixVars :: Eq a => [Term a] -> [Term a]
-- fixVars x = fix x'
--   where
--     x' = reverse x
--
--     -- this is not obviously correct (or is it incorrect?)
--     fix [] = []
--     fix (h : vs) | h == hole = rotate (fix vs)
--     fix (v : vs) = v : fix vs
--
--     rotate [] = []
--     rotate z = last z : init z

class OfItem a where
  finish :: [Term a] -> Ty -> a
  mkVar :: Var -> a
  mkPred :: Pred -> a

type Stack a = [a]

-- Parse state. left side: progress, right side: input sentence.
type St a = (Stack (Item a), Stack (Item a))
data St' a = StNil { stVal :: St a } | St { stVal :: St a, stTail :: (St' a) }
  deriving (Eq, Show)

type M b a = ExceptT String (WriterT [Atom b] (StateT Int [])) a

finish' [] args ty = pure $ finish args ty
finish' ctxt args ty = completeParse (ctxt, [ItemAtom [] args [] ty])

step :: (OfItem a, Eq a, Show a) => St a -> M a (St a)

-- [nondeterminism in lexicon]
--   We handle words that have multiple possible arities here.
step (l, Items ts : r) = do
  t <- lift $ lift $ lift $ ts
  pure (l, t : r)

-- Introduce join
step (lt@(ItemAtom _ _ [ty] _ : _), rt@(ItemAtom _ _ (ty':_) _ : _)) | ty == ty' = do
  v <- mkVar <$> fresh'
  pure (lt, _var v : _comma : _var v : rt)
step (lt@(ItemAtom _ _ (ty':_) _) : l, rt@(ItemAtom _ _ [ty] _) : r) | ty == ty' = do
  v <- mkVar <$> fresh'
  pure (rt : l, _var v : _comma : _var v : lt : r)
  -- pure (x2 : l, x1 : r)

-- Apply to term
step ((ItemAtom termCtxt args [] ty : l), (ItemAtom otherCtxt bound (ty':minusOne) outTy : r)) | ty == ty' = do
  t <- finish' termCtxt args ty
  pure (l, ItemAtom otherCtxt (bound <> [Term $ t]) minusOne outTy : r)
step (ItemAtom otherCtxt bound (ty':minusOne) outTy : l, (ItemAtom termCtxt args [] ty : r)) | ty == ty' = do
  t <- finish' termCtxt args ty
  pure (l, ItemAtom otherCtxt (bound <> [Term $ t]) minusOne outTy : r)
  -- step (x2 : l, x1 : r)

--step (ItemAtom p vs a : l,  ItemHole : r) =
--  pure (l, ItemAtom p (hole : vs) a : r)
--step (ItemHole : l, ItemAtom p vs a : r) =
--  pure (l, ItemAtom p (hole : vs) a : r)

-- [paren handling]
step (l, ItemPush : r)               = pure (ItemPush : l, r)
step (l, ItemPop : r) = do
  case doPop l of
    Just ([x], l') -> pure (l', x : r)
    Just (ItemAtom [] args arity ty:xs, l') -> pure (l',  ItemAtom xs args arity ty : r)
    Just (_bad:_xs, _l') -> throwError $ "todo: " <> show _bad
    Just ([], _) -> throwError "empty parens"
    Nothing -> throwError $ "mismatched ')':\n" <> show l
-- step (x : ItemPush : l, ItemPop : r) = pure (l, x : r)
-- step s@(_, ItemPop : _)              = throwError $ "mismatched ')':\n" <> show s

-- [push step]
--   Otherwise, push the next word to the stack
step (l, w@(ItemAtom {}) : r) = pure (w : l, r)
step (l, w@(ItemHole {}) : r) = pure (w : l, r)

-- [done]
step (s, []) = pure (s, [])

doPop l =
  let (xs, r) = span (/= ItemPush) l
   in case r of
        ItemPush : rest -> Just (xs, rest)
        _ -> Nothing

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

steps :: (OfItem a, Eq a, Show a) => St a -> M a [St a]
steps = iter $ wrap step

completeParse s = do
  s' <- steps s
  case last s' of
    ([ItemAtom ctxt args [] ty], []) -> finish' ctxt args ty
    fin -> throwError $ "todo2: " <> show fin

run1'' :: (Eq a, Show a, OfItem a) => [Item a] -> [Either String [St' a]]
run1'' ws = map (fst . fst) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
    out <- iter' 80 (wrap step') (StNil ([], ws))
    pure out

run1' :: (Eq a, Show a, OfItem a) => [Item a] -> [Either String [St a]]
run1' ws = map (fst . fst) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
    out <- iter' 80 (wrap step) ([], ws)
    pure out

run1 :: (Eq a, Show a, OfItem a) => [Item a] -> [ParseResult a a]
run1 ws = map (check) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
    out <- iter (wrap step) ([], ws)
    let out' = last out
    case out' of
      ([], []) -> pure Nothing
      --([t], []) -> pure $ Just t
      ([ItemAtom ctxt args [] ty], []) -> Just <$> finish' ctxt args ty
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

run3 f =
  case run2 f of
    Success1 _ t : _ -> putStrLn $ pwrap f <> " ok: " <> show t
    Error str _ : _ -> do
      let msg = "failed: " <> f <> "\n" <> str
      putStrLn msg
    _ -> error "todo"

runCatShelf base = do
  f <- readFile (base <> ".turn")
  run3 f

data JoinOp = Binary String String | Fixed String
  deriving (Eq, Show)

specialTokens =
  [ "."
  , "("
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

--efix (TermVar v) = TVar' v
--efix (TermPred p) = TPred' p
efix (Term a) = a
--efix (Term (TVar v)) = TVar' v
--efix (Term (TPred v)) = TPred' v
--efix e = error $ show e
--efix (Term t) = t

-- data T
--   = TVar' Var
--   | TPred' Pred
--   deriving (Eq, Show)

data E
  = Leaf [E] -- e's must be t's
  | Join JoinOp E E
  | TVar Var
  | TPred Pred
  deriving (Eq, Show)

instance OfItem E where
  finish [Term (TPred p), (Term x), (Term y)] ty | ty == _te, Just op <- toJoinOp p = Join op x y
  finish (Term (TPred p) : ts) ty | ty == _te = Leaf (TPred p : map efix ts)
  finish [Term (TVar v)] ty | ty == _t = TVar v
  --finish [TermVar v] ty | ty == _t = TVar v
  finish ts _ = error $ show ts
  mkVar v = TVar v
  mkPred p = TPred p

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

tokenize :: OfItem a => Schema -> Token -> Item a
tokenize _s (Token "(") = ItemPush
tokenize _s (Token ")") = ItemPop
tokenize _s (Token "_") = ItemHole
tokenize _s (Token pr) | Just _ <- toJoinOp pr = _join $ mkPred pr
tokenize _s (Token s@(x : _)) | isUpper x = _var $ mkVar s
tokenize _s (Token s@('_' : _))           = _var $ mkVar s
tokenize  s (Token p@(_ : _)) = Items [ ItemAtom [] [Term $ mkPred p] ar _te | ar <- s p ]
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

printParseResult (Error e _) = putStrLn $ e <> "\n"
printParseResult (Success0 q) = putStrLn $ unlines (map show q)
printParseResult (Success1 q t) = putStrLn $ show t <> "\n" <> unlines (map show q)

tests =
  [ "x/y x y"
  , "x x/y y"
  , "(x/y x) y"
  , "x (y y/x)"
  , "x (z/x/y z) y"
  ]

chk = mapM_ run3 tests
