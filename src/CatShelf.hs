-- Possible alternate names for this:
--    OOOPS = out-of-order predicate syntax
--    FLOPS = flexible-order ...
--    cat shelf = "cat on shelf"
module CatShelf
  ( OfItem, finish, mkVar, mkPred, Term(..)
  , parse, runCatShelf
  , _t, _te, _join, _comma, _var, _infix, _infixTy
  , Pred, Var
  , Item(..), Ty(..)
  , ParseResult(..)
  , tests
  -- todo remove
  , itemTy , isClosed, NormalTy(..) , newJoin
  , exposeL, exposeR
  , Ut(..)
  , uvs
  , tests'
  ) where

import Control.Monad (guard)
import Basic
import Data.Function (on)
import Debug.Trace

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
import Control.Monad.Writer (WriterT, runWriterT, tell, execWriter, Writer)
import Control.Monad.Except
import Data.Char
import Data.Function ((&))
import Data.List
import Data.Maybe
import Data.String
import Text.Read (readMaybe)

type Pred = String
type Var = String

data Term a = Term a
  deriving (Eq, Show, Ord)
data Atom a = Atom Pred [Term a]
  deriving (Eq, Ord, Show)
data Word a = WTerm (Term a) | WPred Pred | WPush | WPop | WHole
  deriving (Eq, Show, Ord)

type ItemStack a = Stack (Item a)

data Ty = Ty String
        -- a \\ b = given a on left, has type b
        | ArrowLeft Ty Ty
        -- b // a = given a on right, has type b
        | ArrowRight Ty Ty
  deriving (Eq, Show, Ord)

data NormalTy = ItemTy { tLeft :: [Ty], tResult :: Ty, tRight :: [Ty] }
  deriving (Eq, Show, Ord)

type T a = Item a
data Item a
  = ItemHole
  | Items [Item a] | ItemPush | ItemPop

  -- | ItemFn a Ty
  | ItemCons a Ty
  | MacroAnd Ty
  | ItemAbsL Ty (Item a)
  | ItemAbsR (Item a) Ty
  | ItemAppLeft (T a) (Item a)
  | ItemAppRight (Item a) (T a)
  | ItemTodo (Item a) (ItemStack a)
  | ItemVar Var Ty
  | ItemPred Pred
  deriving (Show, Eq)

instance OfItem a => IsString (Term a) where
  fromString = Term . mkPred

-- lexicon
_t = Ty "term"
_te = Ty "turn-expr"
_infix op l o r = ItemAbsL l $ ItemAbsR (ItemCons op o) r
_infixTy l o r = ArrowLeft l $ ArrowRight o r
_join op = _infix op _te _te _te
_comma :: OfItem a => Item a
_comma = _join (mkPred ",")
_var v ty = ItemVar v ty -- ItemFn (v) (ItemTy [] _t [])

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
  pp (ItemAppLeft t i) = pp t <> "\\" <> pp i
  pp (ItemAppRight i t) = pp i <> "/" <> pp t
  pp (ItemTodo x r) = pp x <> brwrap (pp r)
  pp (ItemVar v _) = v
  pp (ItemPred p) = p
  pp (ItemHole) = "_"
  pp (ItemCons c _) = pp c
  --pp (ItemAbsL ty i) = pwrap $ pp ty <> "\\\\" <> pp i
  pp (ItemAbsL _ty i) = pp i
  --pp (ItemAbsR i ty) = pwrap $ pp i <> "//" <> pp ty
  pp (ItemAbsR i _ty) = pp i
  pp (MacroAnd _) = "+"

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

pushL x (ItemTy l t r) = ItemTy (x:l) t r
pushR x (ItemTy l t r) = ItemTy l t (x:r)

tyNormalize (Ty s) = ItemTy [] (Ty s) []
tyNormalize (ArrowLeft l r) = pushL l (tyNormalize r)
tyNormalize (ArrowRight l r) = pushR r (tyNormalize l)

-- conflate "mono-sided" arrow types
teq x y = normal x == normal y
  where
    normal (ItemTy [] t r) = ([], r, t)
    normal (ItemTy l t []) = ([], l, t)
    normal (ItemTy l t r)  = (l, r, t)

teqn = on teq tyNormalize

exposeL Ty{} = Nothing
exposeL (ArrowLeft ty t) = Just (ty, t)
exposeL (ArrowRight t tr) = do
  (tl, t') <- exposeL t
  pure (tl, ArrowRight t' tr)
exposeR Ty{} = Nothing
exposeR (ArrowRight t ty) = Just (ty, t)
exposeR (ArrowLeft tl t) = do
  (tr, t') <- exposeR t
  pure (tr, ArrowLeft tl t')
itemTy :: T a -> Maybe Ty
itemTy (ItemAppLeft il ir) = do
  ty <- itemTy il
  (ty', rest) <- exposeL =<< itemTy ir
  guard (ty `teqn` ty')
  pure rest
itemTy (ItemAppRight il ir) = do
  ty <- itemTy ir
  (ty', rest) <- exposeR =<< itemTy il
  guard $ ty' `teqn` ty
  pure rest
itemTy (Items is) = do
  (ty : types) <- mapM itemTy is
  guard $ all (ty ==) types
  pure ty
itemTy ItemHole = pure $ _t
-- as we're parsing, we care about the type of i (the active item)
-- ultimately this item will have a different effect on the stack
itemTy (ItemTodo i _) = itemTy i
itemTy ItemPush = Nothing
itemTy ItemPop = Nothing
itemTy (ItemCons _ ty) = Just ty
itemTy (ItemAbsL ty x) = ArrowLeft ty <$> itemTy x
itemTy (ItemAbsR x ty) = flip ArrowRight ty <$> itemTy x
itemTy (ItemVar _ ty) = Just ty
itemTy (ItemPred _) = Just _t
itemTy (MacroAnd ty) = Just ty

itemNormTy = (tyNormalize <$>) . itemTy

appR item t | Just (ItemTy _ _o []) <- itemNormTy item = ItemAppLeft t item
appR item t = ItemAppRight item t
appL t item | Just (ItemTy [] _o _) <- itemNormTy item = ItemAppRight item t
appL t item = ItemAppLeft t item

bindsRight item =
  case itemNormTy item of
    Just (ItemTy l o (t:r)) -> Just (t, ItemTy l o r)
    Just (ItemTy (t : l) o []) -> Just (t, ItemTy l o [])
    _ -> Nothing
bindsLeft item =
  case itemNormTy item of
    Just (ItemTy (t:l) o r) -> Just (t, ItemTy l o r)
    Just (ItemTy [] o (t : r)) -> Just (t, ItemTy [] o r)
    _ -> Nothing

isClosed item = do
  (ItemTy [] t []) <- itemNormTy item
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

macroApply :: ParseTo a => Item a -> Maybe (Item a)
macroApply i = go [] i
  where
    -- (is, x) = go [] [] i
    Just ty = itemTy i
    go acc = \case
      MacroAnd _ ->
        case acc of
          [x, y, var] -> trace ("!! " <> pp acc) $ Just $
            appR (appR _comma (appR x var)) (appR y var)
          _ -> error $ "hey\n" <> show acc <> ":" <> show i --  Nothing -- throwError?
                <> "\n" <> pp i
      ItemCons _ _  -> Nothing
      ItemAbsL _ t -> go acc t
      ItemAbsR t _ -> go acc t
      ItemAppLeft t i' -> go (t:acc) i'
      ItemAppRight i' t -> go (t:acc) i'
      ItemVar _ _ -> Nothing
      t@(ItemTodo {}) -> error $ "unresolved todo: " <> show t <> show (isClosed t) <> show (resolve t) <> show (bindsLeft t)
      e -> error $ "unreachable: " <> show e

--flattenItem i = error $ show (itemTy i) <> "\n" <> show i

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

-- handle ItemTodo nodes
step (l, ri : r) | Just _ <- isClosed ri, Just (todo, ri') <- resolve ri = do
  pure (l <> todo, ri' : r)
step ([l], []) =
  case isClosed l of
    Nothing -> throwError "bad parse"
    Just _ ->
      case resolve l of
        Just (todo, l') -> pure (todo, [l'])
        Nothing -> pure ([l], [])

step (l, ri : r) | Just _ <- isClosed ri, Just ri' <- macroApply ri = pure (l, ri' : r)

-- Apply to term
step (li : l, ri : r)
    | Just (ty, _) <- bindsRight li
    , Just ty' <- itemNormTy ri
    , tyNormalize ty `teq` ty' = do
  pure (l, appR li ri : r)
step (li : l, ri : r)
    | Just ty <- itemNormTy li
    , Just (ty', _) <- bindsLeft ri
    , ty `teq` tyNormalize ty' = do
  pure (l, appL li ri : r)
--step (ItemAtom otherCtxt bound wl (ty':rMinusOne) outTy : l, (ItemAtom termCtxt args [] [] ty : r)) | ty == ty' = do
--  t <- finish' termCtxt args ty
--  pure (l, ItemAtom otherCtxt (bound <> [Term $ t]) wl rMinusOne outTy : r)

-- Introduce join
step (lt@(li : _), rt@(ri : _))
  | Just (ty, _) <- bindsRight li
  , Just (ty', _) <- bindsLeft ri
  , ty `teqn` ty' = do
  v <- fresh "X"
  pure (lt, _var v ty : _comma : _var v ty' : rt)

-- [push step]
--   Otherwise, push the next word to the stack
step (l, w : r) = pure (w : l, r)
--step (l, w@(ItemAtom {}) : r) = pure (w : l, r)
--step (l, w@(ItemHole {}) : r) = pure (w : l, r)

-- [done]
step (s, []) = pure (s, [])

step (l,r) = error $ "3) unreachable?\n" <> pwrap (show l <> " | " <> show r)

flattenItem :: ParseTo a => Item a -> a
flattenItem i = go [] [] i -- finish (o, map flattenItem is, x)
  where
    -- (is, x) = go [] [] i
    Just ty = itemTy i
    go l r = \case
      ItemCons c _  -> finish (ty, map flattenItem (reverse l <> r), c)
      --ItemFn a _ -> (reverse l <> r, a)
      ItemAbsL _ t -> go l r t
      ItemAbsR t _ -> go l r t
      ItemAppLeft t i' -> go (t:l) r i'
      ItemAppRight i' t -> go l (t:r) i'
      ItemVar v _ -> mkVar v
      t@(ItemTodo {}) -> error $ "unresolved todo: " <> show t <> show (isClosed t) <> show (resolve t) <> show (bindsLeft t)
      e -> error $ "unreachable: " <> show e
--flattenItem i = error $ show (itemTy i) <> "\n" <> show i

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
    _ -> throwError $ "bad parse; final state:\n" <> pp (last history)
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


tests =
  [ "p q"
  , "a a/b b/c c"
  , "p (q + r)"
  , "p (/foo F + B bar/p)"
  , "p (/foo F + /bar B)"
  , "p (/foo F + /bar b)"
  ]

tests' =
  [ "a a/b b/c c"
  , "a (a/b b)"
  , "cat & black X"
  , "(cat&black&long) X"
  , "& a b c"
  , "a (b & c)"
  , "a (& b c)"
  , "a (/b B & c)"
  , "a (/b B & /c c)"
  , "a (*/b B & */c c)" -- not needed
  , "a (/b b & /c c)"
  , "a (/b B & /c c/d d/e e)"
  , "q (p p/q)"
  , "f (A a/sum/b B)"
  ]

printParseResult (Error e _) = putStrLn $ e <> "\n"
printParseResult (Success0 q) = putStrLn $ unlines (map show q)
printParseResult (Success1 q t) = putStrLn $ show t <> "\n" <> unlines (map show q)

cr (h : t) = t <> [h]
cr [] = []
data Ut = UA Pred Int [Ut] [Ut] | UV Var | UH | UP Ut Ut | UNil
  deriving (Eq, Show)
isLeaf UH = True
isLeaf UV{} = True
isLeaf UNil = True
isLeaf UA{} = False
isLeaf UP{} = False
tr f t | isLeaf t = tell $ f t
tr f (UP l r) = tr f l >> tr f r
tr f (UA _ _ ls rs) = mapM_ (tr f) (ls <> rs)
tr _ _ = error "unreachable: check isLeaf"
uvs :: Ut -> [Var]
uvs = execWriter . tr f
  where
    f (UV v) = [v]
    f _ = []
fr t = UV $ fromJust $ find (not . (`elem` (uvs t))) [ "x" <> show i | i <- [0..] ]

insertL UH (UA p n ls rs) = UA p n (UH : ls) rs
insertL x  (UA p n ls rs) = UA p (n-1) (x : ls) rs
insertL _ _ = error ""
insertR UH (UA p n ls rs) = UA p n ls (UH : rs)
insertR x  (UA p n ls rs) = UA p (n-1) ls (x : rs)
insertR _ _ = error ""

isTerm UH = True
isTerm UV{} = True
isTerm _ = False
instance Semigroup Ut where
  UNil <> x = x
  x <> UNil = x
  u <> v | isTerm v, Just kr <- stepR u = kr v
  v <> u | isTerm v, Just kl <- stepL u = kl v
  u <> v | Just kl <- stepR u, Just kr <- stepL v =
      let x = fr (UP u v) in UP (kl x) (kr x)
  x <> y = UP x y
instance Monoid Ut where
  mempty = UNil


stepR (UP l r) | Just k <- stepR r = Just (UP l . k)
stepR (UP l r) | Just k <- stepR l = Just (flip UP r . k)
stepR x@(UA _ i _ _) | i > 0 = Just $ \v -> insertR v x
stepR _ = Nothing

stepL (UP l r) | Just k <- stepL l = Just (flip UP r . k)
stepL (UP l r) | Just k <- stepL r = Just (UP l . k)
stepL x@(UA _ i _ _) | i > 0 = Just $ \v -> insertL v x
stepL _ = Nothing

simpl (UP l r) = UP (simpl l) (simpl r)
simpl (UA p i ls rs) = UA p i (fix ls) (fix rs)
  where
    fix (UH : vs) = cr $ fix vs
    fix (v : vs) = v : fix vs
    fix [] =[]
simpl x = x

solve (UP l r) = solve l <> solve r
solve x = x

newJoin :: [Ut] -> Ut
newJoin = simpl . solve . foldl' UP UNil

instance PP Ut where
  pp (UP l r) = pp l <> " " <> pp r
  pp (UA p i ls rs) = (if i > 0 then "[!"<>show i<>"]" else "") <> pwrap (unwords (p : map pp (reverse ls <> rs)))
  pp (UV v) = v
  pp (UH) = "*"
  pp UNil = "."
