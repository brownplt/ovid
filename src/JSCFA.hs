module Main where

import System.Environment
import Ovid.Run (runCFA)
import WebBits.JavaScript.JavaScript (parseJavaScriptFromFile)

main = do
  rawArgs <- getArgs
  let filename = rawArgs !! 0
  parsedStmts <- parseJavaScriptFromFile filename
  result <- runCFA 1 parsedStmts
  return () 
