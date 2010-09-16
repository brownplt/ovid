module Ovid.Testing
  ( testCFAOnHtml
  , testCFGOnHtml
  , labelAt
  , CfaAssertions (..)
  , Value (..)
  , printValue
  , printValues
  , runTestTT
  ) where

import CFA.Class
import CFA.Labels
import CFA.Impl
import Ovid.Abstraction
import System.IO
import Data.InductiveGraph.ListM (buildGraph)
import Data.Maybe (fromJust,catMaybes)
import qualified Data.Foldable as Foldable
import Javascript.Javascript
import Data.Foldable (Foldable)
import Text.ParserCombinators.Parsec.Pos
import Html.PermissiveParser (parseHtmlFromFile)
import Ovid.Analysis
import Ovid.Net (getPageJavascript)
import Ovid.Environment (buildJsEnv,Ann,AdditionalAnnotation)
import Ovid.DOM (topLevelIds)
import Ovid.ConstraintUtils
import Ovid.Derived
import Ovid.Prelude
import Ovid.Types
import Ovid.CFG
import Test.HUnit
import Text.PrettyPrint

printValues lbl = do
  vs <- currentValuesByLabel lbl
  mapM_ (\v -> printValue v >>= \s -> liftIO (hPutStrLn stderr ('\n':(render s)))) vs

printValue (ABuiltin{aBuiltinName=s}) = 
  return $ text $ "<builtin:" ++ s ++ ">"
printValue (ANum n) = return $ double n
printValue (AObject{aObjectX=(PString sp)}) = case unStringPat sp of
  Just s -> return (text (show s))
  Nothing -> return (text "<indeterminate string>")
printValue (AProperty{aPropertyId=id,aPropertyVals=(ValueSet vals)}) = do
  vals <- currentValues vals
  vs <- mapM printValue vals
  return $ text id <> colon <+> (vcat vs) 
printValue (AObject{aObjectProps=props}) = do
  propVals <- currentValues props
  ps <- mapM printValue propVals
  return $ braces $ nest 2 (vcat $ punctuate comma ps)
printValue _ = return (text "<unknow>")

labelAt :: (Foldable t) 
        => [t (SourcePos,Label,a)]
        -> Int -> Int -- ^row and column
        -> Label
labelAt terms line column =
  let match loc = sourceLine loc == line && sourceColumn loc == column
      results = map (Foldable.find (\(loc,_,_) -> match loc)) terms
    in case catMaybes results of
         ((_,lbl,_):_) -> lbl
         [] -> error ("Test.Ovid.Scripts.LabelAt: no term at line " ++
                      show line ++ ", column " ++ show column)

testCFAOnHtml :: (CFADerived (AnalysisT IO) Contour (Value Contour) ())
              => String
              -> Int
              -> String
              -> ([Statement (SourcePos,Label,AdditionalAnnotation)] -> AnalysisT IO ())
              -> Test
testCFAOnHtml msg nCFA filename assertions = TestLabel msg $ TestCase $ do
  parseResult <- liftIO $ parseHtmlFromFile filename
  case parseResult of
    Left err -> fail (show err)
    Right (html,_) -> do
      stmts <- liftIO $ getPageJavascript html
      let doAnalysis = do
            (env',labelledStmts) <- buildJsEnv topLevelIds stmts
            (names,_,_,env,sets,constraints) <- analyzeStatements' nCFA
              (env',labelledStmts) assertions
            return () 
      evalStateT (buildLabels doAnalysis) emptyJsCFAState 
      return ()

testCFGOnHtml :: (CFADerived (ControlFlowGraphT IO) Contour (Value Contour) Branch)
              => String
              -> Int
              -> String
              -> ([Statement (SourcePos,Label,AdditionalAnnotation)] -> 
                  ControlFlowGraphT IO ())
              -> Test
testCFGOnHtml msg nCFA filename assertions = TestLabel msg $ TestCase $ do
  parseResult <- liftIO $ parseHtmlFromFile filename
  case parseResult of
    Left err -> fail (show err)
    Right (html,_) -> do
      stmts <- liftIO $ getPageJavascript html
      let doAnalysis = do
            (env',labelledStmts) <- buildJsEnv topLevelIds stmts
            (names,_,_,env,sets,constraints) <- analyzeStatements' nCFA
              (env',labelledStmts) assertions
            return () 
      buildGraph $ evalStateT (evalStateT (buildLabels doAnalysis) emptyJsCFAState) (makeEmptyCFGState []) 
      return ()
