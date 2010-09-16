-- |This module exports functions for testing the compiler on Flapjax source
-- files.
module Test.FileTests(compileFlapjaxFile,compileFlapjaxFilesIn) where

import System.IO
import System.Directory
import Text.ParserCombinators.Parsec(ParseError,parseFromFile)
import Html.Parser(parse)
import Flapjax.Compiler(compilePage,defaults)
import Computation(Result(..),runComputation)

suffixOf:: Eq a => [a] -> [a] -> Bool
suffixOf suffix string =
  if suffixLen > stringLen then False else suffix' == suffix where 
    stringLen = length string
    suffixLen = length suffix
    suffix'   = drop (stringLen-suffixLen) string
  

withFlapjaxFile:: (FilePath -> IO ()) -> FilePath -> IO ()
withFlapjaxFile action path = do
  exists <- doesFileExist path
  (if exists && (".fj" `suffixOf` path) 
     then action path
     else putStr ("Ignoring " ++ path ++ "\n") >> return ())

compileFlapjaxFile:: FilePath -> IO ()
compileFlapjaxFile path = do
  htmlOrError <- parseFromFile parse path
  (case htmlOrError of
     (Left err)   -> putStr ("Parse error in " ++ path ++ ":\n"
                             ++ (show err) ++ "\n")
     (Right html) -> do (Success _ html) <- runComputation (compilePage defaults html)
                        writeFile (path ++ ".html") (show html))


compileFlapjaxFilesIn:: FilePath -> IO ()
compileFlapjaxFilesIn path = do
  files <- getDirectoryContents path
  putStr $ show (length files) ++ " items in " ++ path ++ "...\n" 
  mapM_ (withFlapjaxFile compileFlapjaxFile) (map ((path ++ "/") ++) files)
