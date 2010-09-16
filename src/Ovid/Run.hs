module Ovid.Run where

import Control.Monad.State.Strict
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Ovid.Environment (extendedStaticEnvironment,Ann,AdditionalAnnotation(..))
import Framework (evalCounter)
import Ovid.Constraints
import WebBits.JavaScript.JavaScript
import CFA
import CFA.Labels (Label (..), unsafeLabelIx)
import Ovid.Abstraction
import Ovid.Prelude (JsCFAState)
import Ovid.ConstraintUtils (emptyJsCFAState)
import Ovid.DOM (topLevelPreprocessing,topLevelIds)
import WebBits.JavaScript.Environment hiding (Ann)

type AnalysisT m a = CfaT Value (StateT (JsCFAState Contour) m) a


makeTopLevelEnv :: M.Map String Label -- ^inferred top-level environemnt of
                                      -- the program.  This environment excludes
                                      -- top-level identifiers that the
                                      -- program does not use.
                -> Label -- ^next available label
                -> (M.Map String Label,Label)
makeTopLevelEnv inferredEnv nextLabel = 
  insertIds topLevelIds (inferredEnv,nextLabel) where
    insertIds [] (env,lbl) = (env,lbl)
    insertIds (id:ids) (env,lbl@(IxLabel ix))= case M.lookup id env of
      Just _ -> insertIds ids (env,lbl) -- used by program, no need to insert
      Nothing -> insertIds ids (M.insert id (IxLabel (ix+1)) env,IxLabel (ix+1))
    insertIds _ _ = error "Run.hs : expected IxLabel"

mergeTopLevelEnv :: M.Map String Label
                 -> Ann
                 -> Ann
mergeTopLevelEnv topLevelEnv (pos,lbl,extra) = (pos,lbl,extra') where
  extra' = case extra of
    NA -> NA 
    -- M.union is left-biased for duplicates.  This preserves shadowing.
    FnA env locals this -> FnA (M.union env topLevelEnv) locals this

-- (inferredEnv,nextLabel)

runCFA :: Int -- ^ length of the contour
       -> [ParsedStatement] 
       -> IO (Cache Value)
runCFA contourLength parsedStmts = do
  let (labelledStmts,env,nextLabel) = extendedStaticEnvironment 0 parsedStmts
  let (topLevelEnv,nextLabel') = makeTopLevelEnv env nextLabel
  let labelledStmts' = map (fmap $ mergeTopLevelEnv topLevelEnv) labelledStmts
  let ce = M.fromList $ map (\lbl -> (lbl,topContour)) 
                            (map snd $ M.toList topLevelEnv)
  let run = runCfa contourLength (fromJust $ unsafeLabelIx nextLabel') $ do
        topLevelEnv <- topLevelPreprocessing topLevelEnv
        st <- lift get
        liftIO $ putStrLn "Basic env:\n"
        liftIO $ mapM_ (putStrLn.show) (M.toList topLevelEnv)
        lift $ put st { jscfasBuiltins = topLevelEnv }
        --
        window <- case M.lookup "window" topLevelEnv of
          Just lbl -> return (lbl,topContour)
          Nothing -> fail "runCFA: could not find window"
        windowSet <- case M.lookup "window-props" topLevelEnv of
          Just lbl -> return (lbl,topContour)
          Nothing -> fail "runCFA: could not find window-props"
        topThis <- case M.lookup "this" topLevelEnv of
          Just lbl -> return (lbl,topContour)
          Nothing -> fail "runCFA: could not find this (global)"
        let props = [(s,(l,topContour)) | (s,l) <- M.toList topLevelEnv, 
                                          s /= "this"]
        mapM_ (\(id,set) -> newValue (AProperty id (ValueSet set)) windowSet) 
              props
        subsetOf window topThis
        --
        mapM_ (stmt ce topContour) labelledStmts'
  (_,cache,_) <- evalStateT run emptyJsCFAState
  return cache
