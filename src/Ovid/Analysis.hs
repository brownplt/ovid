-- |This module brings the pieces of the analysis together. In particular, it specifies concrete instances for the
-- various abstract classes over which the analyses are defined. Therefore, this is a mess.
module Ovid.Analysis (analyzeStatements, analyzeStatements', buildRequestGraph, buildRequestGraphs,
  buildControlFlowGraph, module Ovid.Abstraction, Contour(..), AnnotatedStatement, AnnotatedExpression,
  buildRandomizationAnnotations) where

--{{{ Imports
import Ovid.Prelude
import Data.Tree (rootLabel)
import Data.Generics
import qualified Data.Map as M
import qualified Data.Zipper as Z
import CFA.Class
import CFA.Labels
import CFA.Impl
import Ovid.Constraints
import Ovid.ConstraintUtils
import Ovid.Abstraction
import Ovid.DOM
import Ovid.Environment (buildJsEnv,Ann,EnvTree)
import Ovid.GraphNode
import Ovid.Derived
import Ovid.CFG
import Ovid.Randomization
import Framework
import WebBits.JavaScript.JavaScript (Statement,Expression)
import qualified WebBits.JavaScript.JavaScript as Js
import Data.InductiveGraph.Class
import Data.InductiveGraph.ListM
import Ovid.Types
import qualified Ovid.Interactions as UI
--}}}


-- Trivial instance of 'CFADerived' for when we don't perform a derived analysis.
instance CFADerived (AnalysisT IO) Contour (Value Contour) () where
  callHook _ _ _ _ = return (\_ m -> m)
  asyncHook _ _ _ m _ = m
  exprHook _ _ _ = return ()
  stmtHook _ _ _ = return ()
  branchHook r m = m >>= \a -> return (r,a)
  joinHook _ r = return r
  navigateHook _ = return ()

nodeFilter v = isRequestNode v || isTopNode v || isDebugNode v {- isOrNode v isAndNode v  -}

-- {{{ Single-file (deprecated)
buildRequestGraph :: (MonadIO m)
                  => Int -> [Statement SourcePos] 
                  -> Bool
                  -> m [Vertex (GraphNode Contour)]
buildRequestGraph contourLength stmts retall = do
  let analysisM = do
        resetCFGState "source"
        analyzeStatements contourLength stmts
  let m = evalStateT analysisM (makeEmptyCFGState []) -- don't record any jumps
  ((_,_,_,cache,constraints),allVxs) <- buildGraph m
  ((),filteredVxs) <- buildGraph (filterVertices nodeFilter allVxs)
  return (if retall then allVxs else filteredVxs)

analyzeStatements :: (MonadIO m,
                      CFADerived (AnalysisT m) Contour (Value Contour) r)
                  => Int -> [Statement SourcePos]
                  -> m (M.Map String Label,
                        [Statement Ann],
                        Z.Tree (Env Label),
                        Cache (Value Contour),
                        Constraints (Value Contour) 
                                    (StateT (JsCFAState Contour) m))
analyzeStatements nCFA ss = do
  let doAnalysis = do
        (env',labelledStmts) <- buildJsEnv topLevelIds ss
        (names,fns,branches,env,sets,constraints) <- analyzeStatements' nCFA (env',labelledStmts) (\_ -> return ())
        return (names,labelledStmts,env,sets,constraints)
  result@(_,_,_,cache,constraints) <- 
    evalStateT (buildLabels doAnalysis) emptyJsCFAState 
  return result

-- }}}

verifyApplication r count set = case valuesOf r set of
  [] -> return (count+1)
  otherwise -> return count
  
verifyApplications r fns = do
  warn $ (show (length fns)) ++ " applications.  Verifying applications ..."
  n <- foldM (verifyApplication r) 0 fns
  warn $ (show n) ++ " applications were not performed."

verifyBranches r branchSets = do
  let verify count set = case valuesOf r set of
        [] -> do
          -- warn $ "Empty guard at " ++ show set
          return (count+1) -- no values, nothing happened!
        otherwise -> return count
  warn $ (show $ length branchSets) ++ " test nodes; checking for values ..."
  nEmpty <- foldM verify 0 branchSets
  if nEmpty == 0 
    then warn $ "All tests performed!"
    else warn $ (show nEmpty) ++ " test-sets are empty, their guarded branches were not executed."
  
buildControlFlowGraph :: (MonadIO m) 
                      => Int 
                      -> [String] -- ^recursion check disabled for these files
                      -> [(String,[Statement SourcePos])] 
                      -> m (InductiveGraph (GraphNode Contour), Cache (Value Contour))
buildControlFlowGraph kCFA files fileStmts = do
  -- list of all sources
  let sources = map fst fileStmts
  cfaState <- return $ foldr enableUnlimitedRecursion emptyJsCFAState files 
  cfaState <- return $  foldr enablePreciseArithmetic cfaState files 
  cfaState <- return $ foldr enablePreciseConditionals cfaState files 
  let mkSubgraph (initCounter,cache) (sourceName,stmts) = do 
        let doAnalysis = do
            nextId <- getCounter
            (env,stmts) <- buildJsEnv topLevelIds stmts
            ((names,fns,branches),sets,cts) <- runCFAOnCache kCFA cache (applyCFA (env,stmts))
            return (names,fns,branches,stmts,env,sets,cts)
        resetCFGState sourceName
        warn $ "----- Begining analysis of " ++ sourceName ++ " -----"
        -- buildLabels' is effectively a runStateT that produces (a,Counter).
        ((_,fns,branches,_,_,cache,_),counter) <- evalStateT (buildLabels' initCounter doAnalysis) cfaState
        verifyApplications cache fns
        verifyBranches cache branches
        return (counter,cache)
  let m = evalStateT (foldM mkSubgraph (counterInit,emptyCache) fileStmts) (makeEmptyCFGState sources)
  -- note that the graph monad maintains its own clock.
  ((_,cache),graph) <- buildInductiveGraph m
  -- Rewrite in-CFA representations of requests and responses to post-CFA representations where all values have been
  -- flattened.
  graph <- forM graph (finalizeXHR cache) 
  return (graph,cache)

  
buildRandomizationAnnotations :: MonadIO m
                              => Int
                              -> [String] -- ^recursion check disabled for these files
                              -> [(String,[Statement SourcePos])] 
                              -> m [Vertex (GraphNode Contour)]
buildRandomizationAnnotations kCFA recursionFiles fileStmts  = do
  (cfg,cache) <- buildControlFlowGraph kCFA recursionFiles fileStmts
  randomizationInfo cfg (concatMap snd fileStmts)

                              
buildRequestGraphs :: (MonadIO m)
                  => Int
                  -> [String] -- ^recursion check disabled for these files
                  -> [(String,[Statement SourcePos])] 
                  -> Bool
                  -> m [Vertex (GraphNode Contour)]
buildRequestGraphs kCFA recursionFiles fileStmts isDetailed = do
  (allVxs,_) <- buildControlFlowGraph kCFA recursionFiles fileStmts
  if isDetailed 
    then return (buildGraph' allVxs)
    else do (_,filteredVxs) <- buildGraph (filterVertices nodeFilter (buildGraph' allVxs))
            return filteredVxs 
    
defaultApproxMsg =
  "--no-approximations is not yet implemented. We omit approximations for\n" ++
  "\'../flapjax/flapjax.js\' and \'flapjax/flapjax.js\' by default.\n"


type V = Value Contour
type E = M.Map String Label

applyCFA :: (CFADerived (CfaT V m) Contour V r,
             MonadState (JsCFAState Contour) m,
             MonadIO m) =>
            (Z.Tree (Env Label), [AnnotatedStatement]) -> CfaT V m (E,[(Label,Contour)],[(Label,Contour)])
applyCFA (envTree,labelledStmts) = do
  let topCt = topContour
  let globalLabels = map snd $ M.toList (E.internalMap $ rootLabel envTree)
  addGlobals globalLabels -- ^ store globals for on-demand JavaScript 
  let globalCe = M.fromList $ map (\lbl -> (lbl,topCt)) globalLabels
  let unId (Id _ s) = s
  let makeTopLevelMap envTree = (M.mapKeys unId (E.internalMap $ rootLabel envTree))
  -- Construct the top-level environment (i.e. window)
  topLevelNames <- topLevelPreprocessing (makeTopLevelMap envTree)
  window <- case M.lookup "window" topLevelNames of
    Just lbl -> return (lbl,topCt)
    Nothing -> fail "could not find window"
  windowSet  <- case M.lookup "window-props" topLevelNames of
    Just lbl -> return (lbl,topCt)
    Nothing -> fail "could not find window-props"
  let props = [(s,(l,topContour)) | (Id _ s, l) <- E.toAscList (rootLabel envTree), s /= "this"]
  mapM_ (\(id,set) -> newValue (AProperty id (ValueSet set)) windowSet) props
  this <- E.lookupEnv (rootLabel envTree) (Id () "this")
  subsetOf window (this,topCt)
  cfaState <- lift get
  lift $ put (cfaState { jscfasBuiltins = topLevelNames })
  initialize
  mapM_ (stmt globalCe topContour) labelledStmts
  fns <- getMarkedFunctions
  branches <- getMarkedBranches
  return (topLevelNames,fns,branches)


analyzeStatements' :: (MonadIO m, CFADerived (CfaT V m) Contour V r, MonadState (JsCFAState Contour) m)
                   => Int
                   -> (EnvTree,[AnnotatedStatement])
                   -> ([AnnotatedStatement] -> CfaT V m ())
                   -> CounterT m (E,[(Label,Contour)],[(Label,Contour)],EnvTree, Cache V, Constraints V m) 
analyzeStatements' nCFA (envTree,labelledStmts) postComputation = do
  ((a,fns,branches),sets,constraints) <- runCfa nCFA (applyCFA (envTree,labelledStmts))
  return (a,fns,branches,envTree,sets,constraints)
