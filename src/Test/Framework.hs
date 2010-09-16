module Test.Framework (withFiles) where

import System.IO
import System.Directory

suffixOf:: Eq a => [a] -> [a] -> Bool
suffixOf suffix string =
  if suffixLen > stringLen then False else suffix' == suffix where 
    stringLen = length string
    suffixLen = length suffix
    suffix'   = drop (stringLen-suffixLen) string
  

withFile:: (FilePath -> IO ()) -> String -> FilePath -> IO ()
withFile action suffix path = do
  exists <- doesFileExist path
  if exists && (suffix `suffixOf` path) 
    then action path
    else putStr ("Ignoring " ++ path ++ "\n") >> return ()


withFiles action suffix path = do
  files <- getDirectoryContents path
  mapM_ (withFile action suffix) (map ((path ++ "/") ++) files)
