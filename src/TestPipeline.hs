module TestPipeline where

import Server (compileAndRun)

runTestPipeline :: String -> IO ()
runTestPipeline = compileAndRun
