-- |Javascript pretty-printer.
module Main where

import Ovid.Net (getPageJavascript)
import Javascript.Javascript (parseJavascriptFromFile)
import Html.PermissiveParser (parseHtmlFromFile)
import System.Environment (getArgs)
import Data.List (isSuffixOf)
import Control.Monad
import Framework


buildTime = 
#ifdef __TIME__ 
  __TIME__
#else
#error "__TIME__ is not defined"
#endif

buildDate =
#ifdef __DATE__
  __DATE__
#else
#error "__DATE__ is not defined"
#endif


main = do
  rawArgs <- getArgs
  case rawArgs of
    [arg] -> main' arg
    otherwise -> fail "Expected a single file name as a command-line argument"

main' path | (".html" `isSuffixOf` path || ".lhs" `isSuffixOf` path) = do
  eitherS <- parseHtmlFromFile path
  case eitherS of
    Left parseError -> fail (show parseError)
    Right (html,warnings) -> do
      unless (null warnings)
        (warn $ show warnings)
      stmts <- getPageJavascript html
      putStr (show stmts)
main' path = do
  stmts <- parseJavascriptFromFile path
  putStr (show stmts)

