module Process where

import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WaiWS
import qualified Network.WebSockets as WS
import Network.HTTP.Types (status200, status404)
import Data.Maybe
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as TL
import qualified Data.Text.IO as TIO
import qualified Data.Text.Encoding as TLE
import Control.Exception (catch, SomeException, try)
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.MVar (newEmptyMVar, tryPutMVar, takeMVar, tryTakeMVar)
import Control.Concurrent.STM (TChan, newBroadcastTChanIO, writeTChan, dupTChan, readTChan, atomically)
import Control.Monad (forever)
import System.Process (readProcess)
import System.FSNotify (withManager, watchDir, Event(..))
import System.FilePath (takeFileName)

import Data.Aeson (encode)
import qualified Data.ByteString.Lazy.Char8 as BLC

import Compile (main1, main1')
import Basic
import qualified Derp.Parse as DP
import qualified Derp.Core as D
import DrawDiagram.Layout (Problem(..), I(..), Constraint(..), T(..), IntervalDiagram(..))
import DrawDiagram.Core (writeDiagram)

rustBinary :: FilePath
rustBinary = "rust-derp/target/release/derp"

runRustDerp :: String -> IO String
runRustDerp base = readProcess rustBinary [base ++ ".gen.derp"] ""

termToKey :: D.Term -> String
termToKey t = BLC.unpack (encode t)

toT :: String -> D.Term -> Maybe T
toT "l" arg = Just (L (termToKey arg))
toT "r" arg = Just (R (termToKey arg))
toT _ _     = Nothing

tuplesToProblem :: [D.Tuple] -> Problem T
tuplesToProblem tuples = Problem intervals constraints True
  where
    ids = [arg | [D.TermPred "isId", arg] <- tuples]
    tags =
      [ (i, ty ++ if length r > 0 then " " <> (unwords $ map pp r) else "")
      | i <- ids
      , (D.TermPred ty : a : r) <- tuples, a == i
      , not (ty `elem` ["isId", "last", "moveLt", "moveBefore", "notLast", "move_at"])
      ]
    intervals =
      [ I ty (L k) (R k)
      | [D.TermPred "isId", arg] <- tuples
      , (i, ty) <- tags
      , i == arg
      , let k = termToKey arg
      ]
    constraints = -- [CLt (left i) (right i) | i <- intervals] ++
      eqs ++ lts
    eqs =
      [ CEq t1 t2
      | [D.TermPred "eq", D.TermApp c1 [arg1], D.TermApp c2 [arg2]] <- tuples
      , t1 <- maybeToList (toT c1 arg1)
      , t2 <- maybeToList (toT c2 arg2)
      ]
    lts =
      [ CLt t1 t2
      | [D.TermPred "lt", D.TermApp c1 [arg1], D.TermApp c2 [arg2]] <- tuples
      , t1 <- maybeToList (toT c1 arg1)
      , t2 <- maybeToList (toT c2 arg2)
      ]

processTuples :: String -> [D.Tuple] -> IO ()
processTuples base tuples = do
  let problem = tuplesToProblem tuples
  putStrLn $ "got " ++ show (length (is problem)) ++ " intervals, "
          ++ show (length (cs problem)) ++ " constraints"
  let iD = IntervalDiagram { title = base, content = problem, fn = base }
  writeDiagram iD
  putStrLn $ "wrote " ++ base ++ ".svg"

compileAndRun :: String -> IO [D.Tuple]
compileAndRun base = do
  _ <- main1' base
  _ <- runRustDerp base
  let outDerp = base ++ ".gen.out.derp"
  putStrLn $ "parsing " ++ outDerp ++ "..."
  derpOutput <- readFile outDerp
  let rules = DP.parse derpOutput
      tuples = concatMap D.head rules
  processTuples base tuples
  pure tuples
