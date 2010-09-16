-- |Command-line interface to the Javascript analysis (jsaz).
module Main where

import System.Console.Editline.Readline
import System.Console.GetOpt
import System.Environment
import System.IO
import System.IO.Error
import Data.Char (toLower)
import Data.Maybe (fromJust)
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.List (isPrefixOf,isSuffixOf)
import CFA.Labels (buildLabels)
import CFA.Class
import CFA.Impl
import qualified Data.Zipper as Z
import qualified Data.Map as M
import qualified Data.Set as S
import WebBits.JavaScript.JavaScript (parseJavaScriptFromFile)
import Ovid.Analysis
import Data.List (intersperse)
import WebBits.Html.PermissiveParser (parseHtmlFromFile)
import WebBits.Html.PrettyPrint()
import WebBits.JavaScript.Crawl (getPageJavaScript)
import Data.InductiveGraph.Class (verticesToMzSchemeReadable)
import Data.InductiveGraph.XML (writeGraphML)

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

--------------------------------------------------------------------------------
-- Interpreting command line arguments

data Argument 
  = InputHtml String
  | InputJavascript String
  | OutputScheme String
  | OutputXML String
  | BuildCFG Int
  | ApplyCFA Int
  | BuildRGA Int
  | FullDetail
  | DisableExponentialHacks String
  deriving (Show)

argSpec =
  [ Option ['o'] ["output"] (ReqArg OutputScheme "FILE") "output as a PLT Scheme expression"
  , Option ['x'] ["xml"] (ReqArg OutputXML "FILE") "output as GraphML"
  , Option [] ["cfa"] (ReqArg (ApplyCFA . read) "K") "perform a control flow analysis only"
  , Option [] ["cfg"] (ReqArg (BuildCFG . read) "K") "build a control flow graph"
  , Option [] ["rga"] (ReqArg (BuildRGA . read) "K") "build randomization information"
  , Option [] ["mmx"] (NoArg (error "MMX optimizations require a Pentium MMX processor")) 
           "enable Pentium MMX optimizations"
  , Option [] ["no-dom"] (NoArg $ error "--no-dom is not yet supported")
           "do not include the DOM model"
  , Option ['a'] ["full-detail"] (NoArg FullDetail) "see the analysis in its full glory"
  , Option ['p'] ["no-approximations"] (ReqArg DisableExponentialHacks "FILE") "Disable approximations for this file"
  , Option ['m'] ["html"] (ReqArg InputHtml "FILE") "parse this file as HTML"
  , Option ['j'] ["javascript"] (ReqArg InputJavascript "FILE") "parse this file as Javascript"
  ]
  
usage = concat
  [ "jsaz pre-release (Ovid), built on " ++ buildTime ++ ", " 
     ++ buildDate ++"\n"
  , "Usage: jsaz [options] file ...\n"
  , usageInfo "" argSpec
  , "\n"
  , "Specify multiple files to perform a multi-page analysis.  The type of a\n"
  , "file is determined by its extension.  However, you may use the --html\n"
  , "and --javascript options to force a file to be treated in a particular\n"
  , "way.\n"
  , "\n"
  , "By default, the analysis detects some common calling patterns that cause\n"
  , "exponential time complexity.  --no-approximations disables these checks\n"
  , "for a specified file.  The file may be one that is indirectly included\n"
  , "for analysis (e.g. \"flapjax.js\").\n"
  , "\n"
  , "You may generate a Scheme expression and a GraphML file simultaneously.\n"
  , "However, you can only perform a single type of analysis in a particular\n"
  , "run.\n"
  ]

warn s =  hPutStrLn stderr s

main = do
  catch main' $ \err -> 
    if isUserError err
      then do putStrLn (ioeGetErrorString err)
      else ioError err

main' = do
  rawArgs <- getArgs
  when (null rawArgs) $
    putStrLn usage >> fail "No arguments specified."
  let (args,options,errors) = getOpt RequireOrder argSpec rawArgs
  unless (null errors) $ do
    mapM_ (\e -> putStrLn (show e)) errors
    fail "Could not parse command line arguments."
  (schemeOut,args) <- getSchemeOutputHandle args
  (xmlOut,args) <- getXMLOutputHandle args
  schemeOut <- pickDefaultOutput schemeOut xmlOut
  (analyzeFn,args) <- getAnalysisFunction args
  (isFullGlory,args) <- getFullGlory args
  (noExponentialFiles,args) <- getNoExponentialHacksOn args
  inFiles <- validateInputFiles args options
  result <- analyzeFn isFullGlory noExponentialFiles inFiles
  unless (schemeOut == Nothing) $
    printScheme (fromJust schemeOut) result
  unless (xmlOut == Nothing) $
    printXML (fromJust xmlOut) result
    
getSchemeOutputHandle ((OutputScheme path):rest) = do
  handle <- openFile path WriteMode
  return (Just handle,rest)
getSchemeOutputHandle rest = 
  return (Nothing,rest)

getXMLOutputHandle ((OutputXML path):rest) = do
  handle <- openFile path WriteMode
  return (Just handle,rest)
getXMLOutputHandle rest = 
  return (Nothing,rest)
  
getNoExponentialHacksOn ((DisableExponentialHacks f):args) = do
  (fs,args') <- getNoExponentialHacksOn args
  return (f:fs,args')
getNoExponentialHacksOn args = do
  jsazPath <- getEnv "JSAZ_PATH"
  return ([jsazPath ++ "/DOM.js"],args)

pickDefaultOutput Nothing Nothing = do
  warn $ "No output format specified.  We wil print the result as a Scheme\n"
      ++ "value to standard out."
  return (Just stdout)
pickDefaultOutput schemeOut _ =
  return schemeOut
  
getFullGlory (FullDetail:rest) = return (True,rest)
getFullGlory rest = return (False,rest)
  
getAnalysisFunction ((BuildCFG k):rest) = do
  when (k < 0) $
    fail "argument to --cfg must be non-negative"
  return (doCFG k,rest)
getAnalysisFunction ((ApplyCFA k):rest) = do
  when (k < 0) $
    fail "argument to --cfa must be non-negative"
  return (doCFA k,rest)
getAnalysisFunction ((BuildRGA k):rest) = do
  when (k < 0) $
    fail "argument to --rga must be non-negative"
  return (doRandomization k, rest)
getAnalysisFunction rest = do
  warn $ "Neither --cfa nor --cfg was specified.  We are assuming --cfg=10."
  return (doCFG 10,rest)
  
validateInputFiles args options = do
  let toInput (InputHtml s) = return (HtmlFile s)
      toInput (InputJavascript s) = return (JavascriptFile s)
      toInput _ = fail "Invalid arguments."
  let guessType path = do
        let path' = map toLower path
        if ".html" `isSuffixOf` path' || ".htm" `isSuffixOf` path' 
          then return (HtmlFile path)
          else if ".js" `isSuffixOf` path' 
                 then return (JavascriptFile path')
                 else fail $ "Prefix `" ++ path 
                              ++ "\' with --html or --javascript."
  explicits <- mapM toInput args
  implicits <- mapM guessType options
  return (explicits ++ implicits)
  
------------------------------------------------------------------------------------------------------------------------
-- Running an analysis and printing results

data InputFile = HtmlFile String | JavascriptFile String

getStatements (JavascriptFile path) = do
  stmts <- parseJavascriptFromFile path
  return (path,stmts)
getStatements (HtmlFile path) = do
  eitherS <- parseHtmlFromFile path
  case eitherS of
    Left parseError -> fail (show parseError)
    Right (html,warnings) -> do
      unless (null warnings)
        (warn $ show warnings)
      jsazPath <- getEnv "JSAZ_PATH"
      domStmts <- parseJavaScriptFromFile (jsazPath ++ "/DOM.js")
      stmts <- getPageJavaScript html
      return (path,domStmts ++ stmts)

doCFG _ _ _ [] = 
  fail "No input files were specified."
doCFG nCFA isDetailed noExpFiles files = do
  pathsAndStmts <- mapM getStatements files
  buildRequestGraphs nCFA noExpFiles pathsAndStmts isDetailed
  
doRandomization nCFA isDetailed noExpFiles files = do
  pathsAndStmts <- mapM getStatements files
  buildRandomizationAnnotations nCFA noExpFiles pathsAndStmts
  
doCFA _ _ _ [] = 
  fail "No input files were specified"
doCFA nCFA isDetailed noExpFiles [file] = do
  (_,stmts) <- getStatements file
  _ <- analyzeStatements nCFA stmts
  warn $ "Analysis complete.  We don\'t know how to print all the value sets."
  return []
doCFA _ _ _ _ = do
  fail "Multi-file control flow analysis is not supported on the command-line, you probably want a control flow graph"


  
printScheme handle result = do
  hPutStrLn handle (verticesToMzSchemeReadable result)
  hClose handle

printXML handle result = do
  writeGraphML handle result
  hClose handle
