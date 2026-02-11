{-# LANGUAGE OverloadedStrings #-}
module Server (runServer) where

import Data.Aeson (encode)
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WaiWS
import qualified Network.WebSockets as WS
import Network.HTTP.Types (status200, status404)
import qualified Data.ByteString.Lazy as LBS
import Control.Exception (catch, SomeException)

import qualified Derp.Types as D

port :: Int
port = 8080

runServer :: D.Tuples -> IO ()
runServer tuples = do
  putStrLn $ "Starting server on http://localhost:" <> show port
  html <- LBS.readFile "view.html"
  Warp.run port (app tuples html)

app :: D.Tuples -> LBS.ByteString -> Wai.Application
app tuples html = WaiWS.websocketsOr WS.defaultConnectionOptions (wsApp tuples) (httpApp html)

httpApp :: LBS.ByteString -> Wai.Application
httpApp html req respond =
  case Wai.rawPathInfo req of
    "/" -> respond $ Wai.responseLBS status200
            [("Content-Type", "text/html; charset=utf-8")] html
    _   -> respond $ Wai.responseLBS status404
            [("Content-Type", "text/plain")] "404 Not Found"

wsApp :: D.Tuples -> WS.ServerApp
wsApp tuples pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 (pure ()) $ do
    putStrLn "WebSocket client connected"
    WS.sendTextData conn (encode tuples)
    -- keep alive: read until disconnect
    let loop = do
          _ <- WS.receiveDataMessage conn
          loop
    loop `catch` \(e :: SomeException) ->
      putStrLn $ "WebSocket client disconnected: " <> show e
