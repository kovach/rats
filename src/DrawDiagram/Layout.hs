module DrawDiagram.Layout where

import Data.Maybe
import Data.List (elemIndex, find, nub, nubBy, sort, sortBy)
import Data.Ord (Down(..))
import Data.Ratio (denominator)

-- | A time interval with a type label and optional children.
data Interval = Interval
  { ivStart    :: Rational
  , ivEnd      :: Rational
  , ivNesting  :: Maybe Rational
  , ivType     :: String
  } deriving (Show)

data T = L String | R String deriving (Eq)
data I a = I String a a
data Constraint a
  = CEq a a
  | CLt a a
  deriving Eq

data Problem a = Problem
  { is :: [I a]
  , cs :: [Constraint a] }

prim x = Problem [I x (L x) (R x)] [L x `CLt` R x]
instance Semigroup (Problem a) where
  (Problem i1 c1) <> (Problem i2 c2) = Problem (i1 <> i2) (c1 <> c2)

t1 =
  prim "a" <> prim "b"
  <> Problem [] [ CLt (R "a") (L "b") ]

-- a contains b, a overlaps c (but doesn't contain it), d after c
t2 =
  prim "a" <> prim "b" <> prim "c" <> prim "d"
  <> Problem []
    [ CLt (L "a") (L "b")
    , CLt (R "b") (R "a")
    , CLt (L "c") (R "a")  -- L c < R a  (c starts before a ends)
    , CLt (L "a") (L "c")  -- L a < L c  (c starts after a)
    , CLt (R "a") (R "c")  -- R a < R c  (c ends after a)   => overlap, not contained
    , CLt (R "c") (L "d")  -- R c < L d  => d after c
    ]

data IntervalDiagram = IntervalDiagram
  { title :: String
  , content :: Problem T
  }

demoDiagrams =
  [ IntervalDiagram "a / b" $
    prim "a" <> prim "b"
    <> Problem []
      [ CLt (L "a") (L "b")
      , CLt (R "b") (R "a") ]
  , IntervalDiagram "a; b" $
    prim "a" <> prim "b"
    <> Problem []
      [ CLt (R "a") (L "b") ]
  , IntervalDiagram "a, b" $
    prim "a" <> prim "b"
    <> Problem []
      [ CLt (L "a") (L "b")
      , CLt (L "b") (R "a")
      , CLt (R "a") (R "b") ]
  , IntervalDiagram "a @ b" $
    prim "a" <> prim "b"
    <> Problem []
      [ CLt (L "a") (L "b")
      , CLt (L "b") (R "a") ]
  , IntervalDiagram "a ~> b" $
    prim "a" <> prim "b"
    <> Problem []
      [ CLt (L "a") (L "b")
      , CEq (R "a") (R "b") ]
  , IntervalDiagram "several" t2
  ]

-- fills in the transitive closure of the `CEq` and `CLt` constraints
saturate :: Eq a => Problem a -> Problem a
saturate (Problem is cs) = Problem is (fixpoint step cs)
  where
    fixpoint f xs =
      let xs' = f xs
      in if length xs' == length xs then xs else fixpoint f xs'
    step cs' = nub $ cs' ++ eqNew ++ ltNew
      where
        -- CEq is symmetric: a=b => b=a
        eqNew = [CEq b a | CEq a b <- cs']
        -- transitivity:
        --   a=b, b=c => a=c
             ++ [CEq a c | CEq a b <- cs', CEq b' c <- cs', b == b']
        --   a=b, b<c => a<c
             ++ [CLt a c | CEq a b <- cs', CLt b' c <- cs', b == b']
        --   a<b, b=c => a<c
             ++ [CLt a c | CLt a b <- cs', CEq b' c <- cs', b == b']
        --   a<b, b<c => a<c
        ltNew = [CLt a c | CLt a b <- cs', CLt b' c <- cs', b == b']
    notIn x xs = not (x `elem` xs)

layout :: Problem T -> [Interval]
layout input = result
  where
    result = verticalLayout $ map (fix bindings) is
    bindings = normalize' $ go [] is

    go bs [] = bs
    go bs (x:xs) = go (updateBindings x bs) xs

    fix bs (I t l r) = Interval (fromJust $ lookup l bs) (fromJust $ lookup r bs) Nothing t

    updateBindings (I _ l r) bs = bindPoint r (bindPoint l bs)

    bindPoint t bs
      | isJust (lookup t bs) = bs
      | otherwise = (t, pickValue t bs) : bs

    Problem {is, cs} = saturate input
    pickValue t bs =
      let lowers = [v | CLt other t' <- cs, t' == t, v <- maybeToList (lookup other bs)]
          uppers = [v | CLt t' other <- cs, t' == t, v <- maybeToList (lookup other bs)]
          eqs    = [v | CEq a b <- cs, let other = if a == t then Just b else if b == t then Just a else Nothing,
                        o <- maybeToList other, v <- maybeToList (lookup o bs)]
          lo = if null lowers then 0 else maximum lowers
          hi = if null uppers then lo + 2 else minimum uppers
      in case eqs of
           (v:_) -> v
           []    -> 1/2 * lo + 1/2 * hi

    -- compute the lcm of the denominators of every value in bs. multiply through by that so that they are all integral
    normalize bs =
      let d = foldl (\acc (_, v) -> lcm acc (denominator v)) 1 bs
      in map (\(t, v) -> (t, v * fromIntegral d)) bs

    -- sort the values in bs, and replace each one with its position in the sort
    normalize' bs =
      let vals = sort $ nub $ map snd bs
          rank v = fromIntegral $ fromJust $ elemIndex v vals
      in map (\(t, v) -> (t, rank v)) bs

    -- Assumes that the `ivNesting` of each input is Nothing. Returns the same intervals, but with the values filled in by according the following requirement:
    --   - if i1 and i2 overlap (L i1 < R i2 and L i2 < R i1) then they have different ivNesting
    --   - if they overlap and furthermore i1 is contained in i2 (L i2 < L i1, R i1 < R i2) then the ivNesting of i1 is greater than the ivNesting of i2.
    -- Processes them in order of width, so if a contains b, a is handled first
    verticalLayout :: [Interval] -> [Interval]
    verticalLayout ivs =
      let sorted = sortBy (\a b -> compare (Down (width a)) (Down (width b))) ivs
          width iv = ivEnd iv - ivStart iv
          overlaps a b = ivStart a <= ivEnd b && ivStart b <= ivEnd a
          assign [] acc = acc
          assign (iv:rest) acc =
            let taken = [n | a <- acc, overlaps iv a, n <- maybeToList (ivNesting a)]
                level = fromJust $ find (`notElem` taken) [0..]
            in assign rest (iv { ivNesting = Just level } : acc)
      in assign sorted []
