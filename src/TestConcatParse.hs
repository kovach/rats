module TestConcatParse where

import Control.Monad ( foldM, when )
import Control.Exception ( catch, IOException )
import System.IO.Error ( isDoesNotExistError )
import Data.List ( partition )
import qualified Data.Map.Strict as Map

import Compile
import ConcatParse
import Basic (PP(..))

readFileOrEmpty :: FilePath -> IO String
readFileOrEmpty path = readFile path `catch` \e ->
  if isDoesNotExistError (e :: IOException) then pure "" else ioError e

runTest :: (Show a, Read a, PP a) => (String -> a) -> (a -> a -> Bool) -> FilePath -> FilePath -> IO ()
runTest test equiv input expected = do
  inputs     <- lines <$> readFile input
  expectedMap <- Map.fromList . map read . lines <$> readFileOrEmpty expected
  let results       = map (\i -> (i, test i)) inputs
      (known, new)  = partition (\(i, _) -> Map.member i expectedMap) results
      ok            = Prelude.all (\(i, actual) -> equiv actual (expectedMap Map.! i)) known
      orphaned      = filter (`notElem` inputs) (Map.keys expectedMap)
  if ok then pure () else putStrLn "failed"
  when (not (null orphaned)) $ do
    putStrLn $ show (length orphaned) <> " golden(s) with no matching input (ignored):"
    mapM_ putStrLn orphaned
  when (ok && not (null new)) $ do
    let newLines = map show new
    putStrLn $ "appending " <> show (length new) <> " new golden(s):"
    mapM_ (putStrLn . pp . snd) new
    appendFile expected $ unlines newLines

newTestConcat = runTest (\x -> case tfx' x of [w] -> w; _ -> Nil) alphaEquiv "hs-test-files/concat-parse-test.txt" "hs-test-files/concat-parse-test.out.txt"
