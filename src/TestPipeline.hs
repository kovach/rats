module TestPipeline where

import Process (compileAndRun)

runTestPipeline :: String -> IO ()
runTestPipeline s = compileAndRun s >> pure ()
