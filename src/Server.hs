{-# LANGUAGE OverloadedStrings #-}
module Server (runServer, runRustDerp, compileAndRun, watchAndRun) where

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

import Compile (main1)
import qualified Derp.Parse as DP
import qualified Derp.Core as D
import DrawDiagram.Layout (Problem(..), I(..), Constraint(..), T(..), IntervalDiagram(..))
import DrawDiagram.Core (writeDiagram)

rustBinary :: FilePath
rustBinary = "rust-derp/target/release/derp"

runRustDerp :: String -> IO String
runRustDerp base = readProcess rustBinary [base ++ ".derp"] ""

compileAndRun :: String -> IO ()
compileAndRun base = do
  _ <- main1 base
  _ <- runRustDerp base
  let outDerp = base ++ ".out.derp"
  putStrLn $ "parsing " ++ outDerp ++ "..."
  derpOutput <- readFile outDerp
  let rules = DP.parse derpOutput
      tuples = concatMap D.head rules
  processTuples base tuples

processTuples :: String -> [D.Tuple] -> IO ()
processTuples base tuples = do
  let problem = tuplesToProblem tuples
  putStrLn $ "got " ++ show (length (is problem)) ++ " intervals, "
          ++ show (length (cs problem)) ++ " constraints"
  let iD = IntervalDiagram { title = base, content = problem }
  writeDiagram (base ++ ".svg") iD
  putStrLn $ "wrote " ++ base ++ ".svg"

termToKey :: D.Term -> String
termToKey t = BLC.unpack (encode t)

toT :: String -> D.Term -> Maybe T
toT "l" arg = Just (L (termToKey arg))
toT "r" arg = Just (R (termToKey arg))
toT _ _     = Nothing

tuplesToProblem :: [D.Tuple] -> Problem T
tuplesToProblem tuples = Problem intervals constraints
  where
    ids = [arg | [D.TermPred "isId", arg] <- tuples]
    tags =
      [ (i, ty)
      | i <- ids
      , (D.TermPred ty : a : _) <- tuples, a == i
      , not (ty `elem` ["isId", "last", "moveBefore", "notLast", "move_at"])
      ]
    intervals =
      [ I ty (L k) (R k)
      | [D.TermPred "isId", arg] <- tuples
      , (i, ty) <- tags
      , i == arg
      , let k = termToKey arg
      ]
    constraints = eqs ++ lts
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

watchAndRun :: String -> TChan TL.Text -> IO ()
watchAndRun base chan = do
  let turnFile = base ++ ".turn"
      jsonFile = base ++ ".json"
  putStrLn $ "watching " ++ turnFile ++ " for changes..."
  run jsonFile
  signal <- newEmptyMVar
  withManager $ \mgr -> do
    _ <- watchDir mgr "." (isTurnFile turnFile) $ \_ ->
      tryPutMVar signal () >> pure ()
    forever $ do
      takeMVar signal
      threadDelay 100000  -- 100ms debounce
      _ <- tryTakeMVar signal  -- drain any extra signal
      putStrLn $ turnFile ++ " changed, recompiling..."
      result <- try (run jsonFile) :: IO (Either SomeException ())
      case result of
        Left err -> putStrLn $ "error: " <> show err
        Right () -> putStrLn "done."
  where
    isTurnFile turnFile event = takeFileName (eventPath event) == turnFile
    run jsonFile = do
      compileAndRun base
      content <- TIO.readFile jsonFile
      atomically $ writeTChan chan content

port :: Int
port = 8080

runServer :: String -> IO ()
runServer base = do
  chan <- newBroadcastTChanIO
  _ <- forkIO $ watchAndRun base chan
  putStrLn $ "Starting server on http://localhost:" <> show port
  Warp.runSettings (Warp.setPort port $ Warp.setTimeout 0 Warp.defaultSettings) (app base chan)

app :: String -> TChan TL.Text -> Wai.Application
app base chan = WaiWS.websocketsOr WS.defaultConnectionOptions (wsApp base chan) httpApp

httpApp :: Wai.Application
httpApp req respond =
  case Wai.rawPathInfo req of
    "/" -> do
      html <- LBS.readFile "view.html"
      respond $ Wai.responseLBS status200
        [("Content-Type", "text/html; charset=utf-8")] html
    _   -> respond $ Wai.responseLBS status404
            [("Content-Type", "text/plain")] "404 Not Found"

wsApp :: String -> TChan TL.Text -> WS.ServerApp
wsApp base chan pending = do
  conn <- WS.acceptRequest pending
  myChan <- atomically $ dupTChan chan
  WS.withPingThread conn 30 (pure ()) $ do
    putStrLn "WebSocket client connected"
    -- send current results on connect
    current <- try (TIO.readFile (base ++ ".json")) :: IO (Either SomeException TL.Text)
    case current of
      Right txt -> WS.sendTextData conn (TLE.encodeUtf8 txt)
      Left _ -> pure ()
    -- send updates as they arrive
    let loop = do
          txt <- atomically $ readTChan myChan
          WS.sendTextData conn (TLE.encodeUtf8 txt)
          loop
    loop `catch` \(e :: SomeException) ->
      putStrLn $ "WebSocket client disconnected: " <> show e
