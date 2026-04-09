-- Possible alternate names for this:
--    OOOPS = out-of-order predicate syntax
--    FLOPS = flexible-order ...
--    cat shelf = "cat on shelf"
module CatShelf
  ( OfItem, finish, mkVar, mkPred, Term(..)
  , parse, runCatShelf
  , _t, _te, _join, _comma, _var
  , Pred, Var
  , Item(..), ItemTy(..)
  , ParseResult(..)
  -- todo remove
  , itemTy , isClosed
  , Arity, Ty ) where

import Control.Monad (guard)
import Basic

-- TODO dead code

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

import Prelude hiding (Word)
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

data Ty = Ty String deriving (Eq, Show, Ord)
type Arity = [Ty]
data Term a = Term a
  deriving (Eq, Show, Ord)
data Atom a = Atom Pred [Term a]
  deriving (Eq, Ord, Show)
data Word a = WTerm (Term a) | WPred Pred | WPush | WPop | WHole
  deriving (Eq, Show, Ord)

type ItemStack a = Stack (Item a)

data ItemTy = ItemTy { tLeft :: [Ty], tResult :: Ty, tRight :: [Ty] }
  deriving (Show, Eq)

type T a = Item a
data Item a
  -- a partially applied atom with `Arity` missing arguments.
  = ItemAtom
    { todo :: ItemStack a
    , have :: [Term a]
    , wantLeft :: Arity
    , wantRight :: Arity
    , resultType :: Ty }
  | ItemHole

  | Items [Item a] | ItemPush | ItemPop

  | ItemFn a ItemTy
  | ItemAppLeft (T a) (Item a)
  | ItemAppRight (Item a) (T a)
  | ItemTodo (Item a) (ItemStack a)
  | ItemVar Var
  | ItemPred Pred
  | Foo a
  deriving (Show, Eq)

instance OfItem a => IsString (Term a) where
  fromString = Term . mkPred

-- lexicon
_t = Ty "term"
_te = Ty "turn-expr"
_join op = ItemFn op (ItemTy [_te] _te [_te] )
_comma :: OfItem a => Item a
_comma = _join (mkPred ",")
_var v = ItemFn (v) (ItemTy [] _t [])

--holeSymbol = "."
--hole :: OfItem a => a
--hole = mkVar holeSymbol
--split delim s = (takeWhile (/= delim) s, drop 1 $ dropWhile (/= delim) s)
--parseLit s =
--  case readMaybe s of
--    Just i -> LitInt i
--    _ -> LitSym s

-- sh :: Show a => [a] -> String
-- sh = unwords . map show

instance PP Ty where
  pp t = show t
instance PP a => PP (Item a) where
  -- show (ItemTerm v) = show v
  -- show (ItemHole) = holeSymbol
  -- pp (ItemAtom _todo vs l r a) = pwrap $ (sh vs) <> (sh l) <> "\\" <> pp a <> "/" <> (sh r)
  pp (Items ts) = "[" <> intercalate " | " (map pp ts) <> "]"
  pp ItemPush = "push"
  pp ItemPop = "pop"
  pp (ItemFn c (ItemTy l o r)) = pp c -- pwrap $ pp c <> ":" <> pp l <> pp o <> pp r
  pp (ItemAppLeft t i) = pp t <> "\\" <> pp i
  pp (ItemAppRight i t) = pp i <> "/" <> pp t
  pp (ItemTodo x r) = pp x <> bwrap (pp r)
  pp (ItemVar v) = v
  pp (ItemPred p) = p
  pp (ItemHole) = "_"
  pp (ItemAtom {}) = error "todo remove"
  pp (Foo _) = error "todo remove foo"

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
  finish :: (Ty, [a], a) -> a
  mkVar :: Var -> a
  mkPred :: Pred -> a

type ParseTo a = (Eq a, Show a, OfItem a, PP a)

type Stack a = [a]

-- Parse state. left side: progress, right side: input sentence.
type St a = (Stack (Item a), Stack (Item a))
data St' a = StNil { stVal :: St a } | St { stVal :: St a, stTail :: (St' a) }
  deriving (Eq, Show)

type M a = ExceptT String (StateT Int []) a

-- finish' [] args ty = pure $ finish args ty
-- finish' ctxt args ty = completeParse (ctxt, [ItemAtom [] args [] [] ty])

-- finish'' = go [] []
--  where
--    go l r = \case
--      ItemFn cons _ _ ty -> finish (cons <> reverse l <> r) ty
--      ItemAppLeft t i -> go (t:l) r i
--      ItemAppRight i t -> go l (t:r) i
--      ItemTodo i s -> _
--      _ -> error "unreachable"


termTy = ItemTy  [] _t []
itemTy (ItemFn _ ty) = Just ty
itemTy (ItemAppLeft il ir) = do
  (ItemTy [] t []) <- itemTy il
  (l, rest) <- bindsLeft ir
  guard $ t == l
  pure rest
itemTy (ItemAppRight il ir) = do
  (r, rest) <- bindsRight il
  (ItemTy [] t []) <- itemTy ir
  guard $ t == r
  pure rest
itemTy (Items is) = do
  (ty : types) <- mapM itemTy is
  guard $ all (ty ==) types
  pure ty
itemTy ItemHole = pure $ termTy
-- as we're parsing, we care about the type of i (the active item)
-- ultimately this item will have a different effect on the stack
itemTy (ItemTodo i _) = itemTy i
itemTy ItemPush = Nothing
itemTy ItemPop = Nothing
itemTy i = error $ "todo remove: " <> show i -- todo remove other cases

appR item t | Just (ItemTy _ _o []) <- itemTy item = ItemAppLeft t item
appR item t = ItemAppRight item t
appL t item | Just (ItemTy [] _o _) <- itemTy item = ItemAppRight item t
appL t item = ItemAppLeft t item

bindsRight item =
  case itemTy item of
    -- Nothing -> error $ "mistyped: " <> show item
    Just (ItemTy l o (t:r)) -> Just (t, ItemTy l o r)
    Just (ItemTy (t : l) o []) -> Just (t, ItemTy l o [])
    _ -> Nothing
bindsLeft item =
  case itemTy item of
    -- Nothing -> error $ "mistyped: " <> show item
    Just (ItemTy (t:l) o r) -> Just (t, ItemTy l o r)
    Just (ItemTy [] o (t : r)) -> Just (t, ItemTy [] o r)
    _ -> Nothing

isClosed item = do
  (ItemTy [] t []) <- itemTy item
  pure t

resolve :: Item a -> Maybe (ItemStack a, Item a)
resolve = \case
  ItemTodo item rest ->
    Just (rest, item)
    --let (rest', item') = resolve item
    -- in (rest' <> rest, item') -- immmediate rest on top
  ItemAppLeft term item | Just item' <- resolve item -> do
    pure $ ItemAppLeft term <$> item'
  ItemAppLeft term item | Just term' <- resolve term -> do
    pure $ flip ItemAppLeft item <$> term'
  ItemAppRight item term | Just item' <- resolve item -> do
    pure $ flip ItemAppRight term <$> item'
  ItemAppRight item term | Just term' <- resolve term -> do
    pure $ ItemAppRight item <$> term'
  _ -> Nothing
  --(ItemFn {}) -> Nothing
  --Items _ -> error "no"
  --_ -> error "todo"

flattenItem :: ParseTo a => Item a -> a
flattenItem i | Just (ItemTy [] o []) <- itemTy i = finish (o, map flattenItem is, x)
  where
    (is, x) = go [] [] i
    go l r = \case
      ItemFn a _ -> (reverse l <> r, a)
      ItemAppLeft t i' -> go (t:l) r i'
      ItemAppRight i' t -> go l (t:r) i'
      t@(ItemTodo {}) -> error $ "unresolved todo: " <> show t <> show (isClosed t) <> show (resolve t) <> show (bindsLeft t)
      _ -> error "unreachable"
flattenItem i = error $ show (itemTy i) <> "\n" <> show i

step :: ParseTo a => St a -> M (St a)

-- [nondeterminism in lexicon]
--   We handle words that have multiple possible arities here.
step (l, Items ts : r) = do
  t <- lift $ lift $ ts
  pure (l, t : r)

-- [paren handling]
step (l, ItemPush : r)               = pure (ItemPush : l, r)
step (l, ItemPop : r) = do
    case popped of
      Just (t:xs, l') -> pure (l', ItemTodo t xs : r)
      Just ([], _) -> error "empty parens"
      Nothing -> error $ "mismatched ')':\n" <> show l
  where
    popped =
      let (xs, l') = span (/= ItemPush) l
       in case l' of
            ItemPush : l'' -> Just (xs, l'')
            _ -> Nothing

-- step (x : ItemPush : l, ItemPop : r) = pure (l, x : r)
-- step s@(_, ItemPop : _)              = throwError $ "mismatched ')':\n" <> show s

step (l, ri : r) | Just _ <- isClosed ri, Just (todo, ri') <- resolve ri = do
  pure (l <> todo, ri' : r)

-- Apply to term
step (li : l, ri : r)
    | Just (ty,_) <- bindsRight li
    , Just ty' <- isClosed ri
    , ty == ty' = do
  pure (l, appR li ri : r)
step (li : l, ri : r)
    | Just ty <- isClosed li
    , Just (ty', _) <- bindsLeft ri
    , ty == ty' = do
  pure (l, appL li ri : r)
--step (ItemAtom otherCtxt bound wl (ty':rMinusOne) outTy : l, (ItemAtom termCtxt args [] [] ty : r)) | ty == ty' = do
--  t <- finish' termCtxt args ty
--  pure (l, ItemAtom otherCtxt (bound <> [Term $ t]) wl rMinusOne outTy : r)

-- Introduce join
step (lt@(li : _), rt@(ri : _))
  | Just (ty, _) <- bindsRight li
  , Just (ty', _) <- bindsLeft ri, ty == ty' = do
  v <- mkVar <$> fresh "X"
  pure (lt, _var v : _comma : _var v : rt)

-- [push step]
--   Otherwise, push the next word to the stack
step (l, w : r) = pure (w : l, r)
--step (l, w@(ItemAtom {}) : r) = pure (w : l, r)
--step (l, w@(ItemHole {}) : r) = pure (w : l, r)

-- [done]
step (s, []) = pure (s, [])

step (l,r) = error $ "3) unreachable?\n" <> pwrap (show l <> " | " <> show r)

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

steps :: ParseTo a => St a -> M [St a]
steps = iter $ wrap step

-- completeParse s = do
--  s' <- steps s
--  case last s' of
--    ([ItemAtom ctxt args [] [] ty], []) -> finish' ctxt args ty
--    fin -> throwError $ "todo2: " <> show fin

--run1'' :: ParseTo a => [Item a] -> [Either String [St' a]]
--run1'' ws = map (fst . fst) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
--    out <- iter' 80 (wrap step') (StNil ([], ws))
--    pure out
--
--run1' :: ParseTo a => [Item a] -> [Either String [St a]]
--run1' ws = map (fst . fst) $ flip runStateT 0 $ runWriterT $ runExceptT $ do
--    out <- iter' 80 (wrap step) ([], ws)
--    pure out

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

runTrace ws = map fst $ flip runStateT 0 $ runExceptT $ do
  history <- iter (wrap step) ([], ws)
  case last history of
    ([_], []) -> pure history
    _ -> throwError $ "bad parse; final state: " <> pp (last history)
mlast :: PP a => [Either String [St a]] -> [Either String (Item a)]
mlast = map (fmap go)
  where
    go x = case last x of
      ([x], []) -> x
      _ -> error "unreachable [mlast]"
      -- ([ItemAtom ctxt args [] [] ty], []) -> Just <$> finish' ctxt args ty
      --([], []) -> error "empty input"
      --out -> error $ "bad parse. temp term remaining: " <> show out
run1 :: ParseTo a => Stack (Item a) -> [Either String (Item a)]
run1 ws = mlast $ runTrace ws

-- run2 :: String -> [ParseResult E E]
-- run2 = run1 . map (tokenize defaultSchema) . lex

--run3 f =
--  case run2 f of
--    Success1 _ t : _ -> putStrLn $ pwrap f <> " ok: " <> show t
--    Error str _ : _ -> do
--      let msg = "failed: " <> f <> "\n" <> str
--      putStrLn msg
--    _ -> error "todo"


type PR a = Either String a
parse :: ParseTo a => [Item a] -> [PR a]
parse = map (flattenItem <$>) . run1

runCatShelf base = do
  pure ()
  -- f <- readFile (base <> ".turn")
  -- parse f

--efix (TermVar v) = TVar' v
--efix (TermPred p) = TPred' p
--efix (Term (TVar v)) = TVar' v
--efix (Term (TPred v)) = TPred' v
--efix e = error $ show e
--efix (Term t) = t

-- data T
--   = TVar' Var
--   | TPred' Pred
--   deriving (Eq, Show)

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

-- chk = mapM_ run3 tests
