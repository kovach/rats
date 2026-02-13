module Main where

import Prelude hiding (pred, exp, take)
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad
import Data.Monoid (Sum(..))
import Data.List hiding (take)
import qualified Data.List
import Data.Maybe
import Data.Functor.Identity
import Data.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace

import Basic
import Types
import Parser (program)
import ParserCombinator (assertParse, lexComments)
import MMap (MMap)
import qualified MMap as M
import qualified Derp.Core as D
import Derp.Parse
import qualified GenSouffle as GS
import qualified Derp.Gen as GD
import Server (runServer)
import Compile

main = do
  -- tuples <- main3
  runServer
