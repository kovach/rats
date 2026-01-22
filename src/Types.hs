module Types where

import Control.Monad.State
import Data.Monoid (Sum(..))
import Data.Char
import Data.List
import qualified MMap as M
import MMap (MMap)
import Data.Set (Set)
import qualified Data.Set as Set

pwrap x = "(" <> x <> ")"
bwrap x = "[" <> x <> "]"

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
