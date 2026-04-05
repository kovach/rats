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
import Basic
import qualified Derp.Parse as DP
import qualified Derp.Core as D
import DrawDiagram.Layout (Problem(..), I(..), Constraint(..), T(..), IntervalDiagram(..))
import DrawDiagram.Core (writeDiagram)
import Process

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
app base chan = WaiWS.websocketsOr WS.defaultConnectionOptions (wsApp base chan) (httpApp base)

httpApp :: String -> Wai.Application
httpApp base req respond =
  case Wai.rawPathInfo req of
    "/" -> do
      html <- LBS.readFile "view.html"
      respond $ Wai.responseLBS status200
        [("Content-Type", "text/html; charset=utf-8")] html
    "/diagram.svg" -> do
      svg <- LBS.readFile ("diagrams/" ++ base ++ ".svg")
      respond $ Wai.responseLBS status200
        [("Content-Type", "image/svg+xml"), ("Cache-Control", "no-cache")] svg
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
