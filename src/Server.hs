{-# LANGUAGE OverloadedStrings #-}
module Server (runServer, runRustDerp, compileAndRun, watchAndRun) where

import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WaiWS
import qualified Network.WebSockets as WS
import Network.HTTP.Types (status200, status404)
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import Control.Exception (catch, SomeException, try)
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.MVar (newEmptyMVar, tryPutMVar, takeMVar, tryTakeMVar)
import Control.Concurrent.STM (TChan, newBroadcastTChanIO, writeTChan, dupTChan, readTChan, atomically)
import Control.Monad (forever)
import System.Process (readProcess)
import System.FSNotify (withManager, watchDir, Event(..))
import System.FilePath (takeFileName)

import Compile (main1)

rustBinary :: FilePath
rustBinary = "rust-derp/target/release/derp"

runRustDerp :: IO String
runRustDerp = readProcess rustBinary ["out.derp"] ""

compileAndRun :: IO ()
compileAndRun = do
  _ <- main1
  output <- runRustDerp
  writeFile "out.tuples" output

watchAndRun :: TChan TL.Text -> IO ()
watchAndRun chan = do
  putStrLn "watching ttt.turn for changes..."
  run
  signal <- newEmptyMVar
  withManager $ \mgr -> do
    _ <- watchDir mgr "." isTttTurn $ \_ ->
      tryPutMVar signal () >> pure ()
    forever $ do
      takeMVar signal
      threadDelay 100000  -- 100ms debounce
      _ <- tryTakeMVar signal  -- drain any extra signal
      putStrLn "ttt.turn changed, recompiling..."
      result <- try run :: IO (Either SomeException ())
      case result of
        Left err -> putStrLn $ "error: " <> show err
        Right () -> putStrLn "done."
  where
    isTttTurn event = takeFileName (eventPath event) == "ttt.turn"
    run = do
      compileAndRun
      content <- TL.pack <$> readFile "out.tuples"
      atomically $ writeTChan chan content

port :: Int
port = 8080

runServer :: IO ()
runServer = do
  chan <- newBroadcastTChanIO
  _ <- forkIO $ watchAndRun chan
  putStrLn $ "Starting server on http://localhost:" <> show port
  -- Warp.run port (app chan)
  Warp.runSettings (Warp.setPort port $ Warp.setTimeout 0 Warp.defaultSettings) (app chan)

app :: TChan TL.Text -> Wai.Application
app chan = WaiWS.websocketsOr WS.defaultConnectionOptions (wsApp chan) httpApp

httpApp :: Wai.Application
httpApp req respond =
  case Wai.rawPathInfo req of
    "/" -> do
      html <- LBS.readFile "view.html"
      respond $ Wai.responseLBS status200
        [("Content-Type", "text/html; charset=utf-8")] html
    _   -> respond $ Wai.responseLBS status404
            [("Content-Type", "text/plain")] "404 Not Found"

wsApp :: TChan TL.Text -> WS.ServerApp
wsApp chan pending = do
  conn <- WS.acceptRequest pending
  myChan <- atomically $ dupTChan chan
  WS.withPingThread conn 30 (pure ()) $ do
    putStrLn "WebSocket client connected"
    -- send current tuples on connect
    current <- try (TL.pack <$> readFile "out.tuples") :: IO (Either SomeException TL.Text)
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
