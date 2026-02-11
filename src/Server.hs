{-# LANGUAGE OverloadedStrings #-}
module Server (runServer) where

import Data.Aeson (ToJSON(..), Value(..), object, (.=), encode)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Key
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WaiWS
import qualified Network.WebSockets as WS
import Network.HTTP.Types (status200, status404)
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as T
import Data.IORef
import Control.Monad (forever)
import Control.Exception (catch, SomeException)

port :: Int
port = 8080

runServer :: IO ()
runServer = do
  putStrLn $ "Starting server on http://localhost:" <> show port
  Warp.run port app

app :: Wai.Application
app = WaiWS.websocketsOr WS.defaultConnectionOptions wsApp httpApp

httpApp :: Wai.Application
httpApp _req respond =
  respond $ Wai.responseLBS status200 [("Content-Type", "text/plain")] "rats server"

wsApp :: WS.ServerApp
wsApp pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 (pure ()) $ do
    putStrLn "WebSocket client connected"
    let loop = do
          msg <- WS.receiveData conn :: IO T.Text
          putStrLn $ "Received: " <> T.unpack msg
          WS.sendTextData conn ("{\"echo\":" <> encode (String msg) <> "}" :: LBS.ByteString)
          loop
    loop `catch` \(e :: SomeException) ->
      putStrLn $ "WebSocket client disconnected: " <> show e
