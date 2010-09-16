-- |Generates a control flow graph alongside a control flow analysis.
module Ovid.CFG
  ( ControlFlowGraphT
  , resetCFGState
  , makeEmptyCFGState
  , Branch
  ) where
  
import Control.Monad.Identity
import Control.Monad.Reader
import Framework
import WebBits.JavaScript.JavaScript hiding (Expression,Statement)
import qualified WebBits.JavaScript.JavaScript as Js
import qualified Data.Map as M
import qualified Data.Foldable as F
import Data.Generics
import Data.Typeable
import Data.Maybe
import Ovid.Environment (Ann)
import Ovid.Derived
import CFA.Labels hiding (newLabel)
import Ovid.Abstraction
import CFA
import Data.InductiveGraph.Class
import Data.InductiveGraph.ListM (GraphT,Node,firstNode)
import Ovid.ConstraintUtils
import Ovid.GraphNode
import Ovid.Types
import Ovid.Prelude
import qualified Ovid.Interactions as UI

-- #define DEBUG_ASYNC
-- #define TRACE_STATE_CHANGE
-- #define DEBUG_CALL
-- #define TRACE_STATE
-- #define TRACE_GET_STATE

-- type AnalysisT m = CfaT (Value Contour) (StateT (JsCFAState Contour) m)
type CfgT m = StateT CFGState (GraphT GraphNode m)

type ControlFlowGraphT m =
  AnalysisT (StateT CFGState (GraphT GraphNode m))

data CFGState = CFGState {
  lastVx :: Node,
  -- |first vertex in this event path
  firstVx :: Node, 
  -- |disambiguates distinct jump points to the same page
  lastNavIx :: Int,
  -- |Names of pages being analyzed.  This is used to determine whether or not
  -- to record a jump.
  cfgSources :: [String]
} deriving (Show)

-- |Value used to handle branching.
data Branch
  = Branch Node {- branching vertex -} Node {- join -} Node {- parent of branching vertex -}
  | BranchPath Node {- end vertex of the branch path -}
  | NoBranch

-- | Returns the first annotation, which is the annotation at the head.
type V = Value
type N = GraphNode

makeEmptyCFGState :: [String] -> CFGState
makeEmptyCFGState sources = CFGState firstNode firstNode 0 sources

getState :: MonadIO m
         => (ControlFlowGraphT m) CFGState
getState = do
  s <- lift2 get
{- #ifdef  TRACE_GET_STATE
  liftIO $ putStrLn $ "get-state: " ++ show s
 #endif -}
  return s

putState :: MonadIO m
         => String -> CFGState -> (ControlFlowGraphT m) ()
putState msg s = do
{- #ifdef  TRACE_STATE_CHANGE
  s' <- lift2 get
  when (firstVx s' /= firstVx s)
    (liftIO $ putStrLn $ "firstVx changing from " ++ show (firstVx s') 
       ++ " to " ++ show (firstVx s) ++ "; reason: " ++ msg)
 #endif -}
  lift2 (put s)
{- #ifdef  TRACE_STATE
  liftIO $ putStrLn $ "put-state: " ++ msg ++ "; " ++ show s
 #endif -}

-- |Resets the graph builder's state.  This is used to build multiple subgraphs
-- in the same data structure (i.e. analyzing multiple pages).
resetCFGState :: (MonadIO m)
              => String -- ^name of the source file we are about to analyze
              -> CfgT m ()
resetCFGState sourceName = do
  state <- get
  vxTop <- lift $ newNode (TopNode sourceName)
  put $ state {lastVx=vxTop,firstVx=vxTop}

instance (Monad m, MonadIO m) => CFADerived (ControlFlowGraphT m) 
                                  Value Branch where
  callHook fn args ct result = do
    -- statically determined parent at the point of application
    st@CFGState{lastVx=callSiteVx,firstVx=callFirstVx} <- getState
    -- statically determined return site for function calls
    joinVx <- lift3 $ newNode (JoinNode (fst fn,ct))
    -- continue at return point
    putState "continuing" (st {lastVx=joinVx})
    -- A "dotted edge" that indicates that control flows even if the set is
    -- empty.  We remove it if we have an actual value.
    lift3 $ newEdge () callSiteVx joinVx 
{- #ifdef  DEBUG_CALL
    liftIO $ putStrLn $ "call site for " ++ show fn ++ "; call= "
      ++ show callSiteVx ++ "; first=" ++ show callFirstVx
 #endif -}
    return $ \fn m -> case functionLabel fn of
      Just lbl -> do
        st@CFGState{lastVx=savedVx,firstVx=savedFirstVx} <- getState
        -- the call was made to this function
        inVx <- if isBuiltinLabel lbl && labelName lbl == (Just "print") then do
                  lift3 $ newNode (DebugNode "" (head args) (lbl,ct))
                else
                  lift3 $ newNode (ClientCallNode (lbl,ct))
        lift3 $ newEdge () callSiteVx inVx 
        -- analyze the body (m) with inVx as the entry point
        putState "restoring defn point" (st {lastVx=inVx,firstVx=callFirstVx})
{- #ifdef  DEBUG_CALL
        unless (isBuiltin fn)
          (liftIO $ putStrLn $ "applying " ++ show (aFunctionArgs fn) 
             ++ "; restoring" ++ show st)
 #endif -}
        a <- m -- function
        -- last vertex in the function body
        st@CFGState{lastVx=lastVx} <- getState 
        returnVx <- lift3 $ newNode (ClientReturnNode (lbl,ct))
        if lastVx == joinVx
          then lift3 $ newEdge () inVx returnVx
          else lift3 $ newEdge () lastVx returnVx
        lift3 $ newEdge () returnVx joinVx
        -- since we now have a sensible path from callSiteVx to joinVx, we
        -- can safely delete the "dotted edge."
        -- If the edge is not removed, it has been removed in by an earlier
        -- value.
        edgeRemoved <- lift3 $ removeEdge () callSiteVx joinVx
        -- when (not edgeRemoved) (fail "could not remove implicit edge (bug)")
         -- restore state
        putState "restoring call point" (st {lastVx=savedVx,firstVx=savedFirstVx})
        return a        
      Nothing -> m
  
  -- asynchronous request to the server --
  asyncHook ct this cxt m True {- server call -} = do
    -- We know that an enclosing callHook has set the parent vertex correctly. eventVx is the node where processing of 
    -- this event started.  inVx is the point in the graph where we are about to send an asynchonous request to the
    -- server.  The computation m generates the call graph of execution that occurs after the server responds.
    CFGState{lastVx=inVx,firstVx=eventVx} <- getState
    -- Create the server-request node, scnVx.  The request is made here, immediately after inVx.  The event is
    -- repeatable if it was triggered directly by a DOM event.
    lastEvent <- lift3 $ nodeValue eventVx
    scnVx <- lift3 $ newNode (ServerCallNode (EqualOrd []) (EqualOrd []) (isDomEventNode lastEvent) cxt)
    lift3 $ newEdge () inVx scnVx
    -- construct the set of urls and contents
    unsafePropagatePropertyValue this cxt "url" $ \url -> 
      lift3 $ updateNode scnVx (\n -> n { scnUrl = eovUpd (url:) (scnUrl n) })
    unsafePropagatePropertyValue this cxt "content" $ \content -> 
      lift3 $ updateNode scnVx (\n -> n { scnContent = eovUpd (content:) (scnContent n) })
    -- Create the server-response vertex, respVx.  The response may arrive immediately after the request, scnVx.
    respVx <- lift3 $ newNode (ServerResponseNode (EqualOrd []) cxt)
    lift3 $ newEdge () scnVx respVx
    -- compute the shape of the response
    unsafePropagatePropertyValue this cxt "responseText" $ \r -> 
      lift3 $ updateNode respVx  (\vx -> vx { srnValues = eovUpd (r:) (srnValues vx) })
    -- Generate the subgraph of computation that occurs when the server responds.
    st <- getState
    putState "setting scn point" (st{lastVx=respVx,firstVx=respVx})
    a <- m
    -- Restore the previous state.
    putState "restoring async call pt" st
{- #ifdef  DEBUG_ASYNC
    liftIO $ putStrLn $ "Ending async call with firstVx=" ++ show scnVx
 #endif -}
    return a
  -- client-side asynchrony --
  asyncHook ct this cxt m False = do
    -- We know that an enclosing callHook has set the parent vertex correctly. eventVx is node where processing of this
    -- event started.  The event handler is called at some point after the currently executing strand of execution.
    -- Hence, it is parallel to this strand.
    st@CFGState{lastVx=inVx,firstVx=eventVx,lastNavIx=ix} <- getState
    domVx <- lift3 $ newNode (DomEventNode ix)
    lift3 $ newEdge () eventVx domVx 
    putState "setting scn point" (st{lastVx=domVx,firstVx=domVx,lastNavIx=ix+1})
{- #ifdef  DEBUG_ASYNC
    liftIO $ putStrLn $ "client-side async call: firstVx=" ++ show eventVx
 #endif -}
    a <- m
    st@CFGState{lastNavIx=ix} <- getState
    putState "restoring async call pt" st{lastNavIx=ix}
    return a
  
  exprHook ce ct (CondExpr (_,lbl,_) _ _ _) = do
    CFGState{lastVx=lastVx} <- getState
    branchVx <- lift3 $ newNode (OrBranchNode (lbl,ct))
    joinVx <- lift3 $ newNode (JoinNode (lbl,ct))
    return (Branch branchVx joinVx lastVx)
  exprHook ce ct e = do 
    return NoBranch
    
  stmtHook ce ct (IfStmt (_,lbl,_) _ _ _) = do
    CFGState{lastVx=lastVx} <- getState
    branchVx <- lift3 $ newNode (OrBranchNode (lbl,ct))
    joinVx <- lift3 $ newNode (JoinNode (lbl,ct))
    return (Branch branchVx joinVx lastVx)
  stmtHook _ _ _ = return NoBranch
    
  branchHook (Branch branchVx joinVx branchParentVx) m = do
    lift3 $ newEdge () branchParentVx branchVx -- TODO: ensure single add
    -- set the parent of the branch
    st <- getState
    putState "branching" (st{lastVx=branchVx})
    -- analyze
    a <- m
    -- join path-end vertex to joinVx and return the vertex at the end of the
    -- branch-path
    CFGState{lastVx=lastVx} <- getState
    lift3 $ newEdge () lastVx joinVx
    return (BranchPath lastVx,a)
  branchHook branch _ = fail "branchHook expected a Branch (bug)"
    
  joinHook paths (Branch _ joinVx _) = do
    st <- getState
    putState "joining" (st{lastVx=joinVx})
    return ()    
  joinHook _ branch = fail "joinHook expected a Branch (bug)"
  
  navigateHook (AObject{aObjectX=(PString sp)}) | isJust (unStringPat sp) = do
    let url = fromJust (unStringPat sp)
    st@CFGState{lastVx=vx,lastNavIx=ix,cfgSources=srcs} <- getState
    -- Check to see if the url matches *any* of the sources we are analyzing
    let options = filter (\src -> src `isPrefixOf` url) srcs
    case options of
      [] -> warn $ "Ignoring the jump to " ++ show url
      srcs -> do
        src <- if null (tail srcs) 
                 then return (head srcs)
                 else do UI.tell $ "The address \"" ++ show url ++ 
                                   "\" matches multiple locations."
                         UI.options srcs
        warn $ "window.location = " ++ url ++ "(canonical: " ++ src ++ ")"
        jumpVx <- lift3 $ newNode (PageNavNode url ix)
        lift3 $ newEdge () vx jumpVx
        destVx <- lift3 $ newNode (TopNode src)
        lift3 $ newEdge () jumpVx destVx
        putState "page jump" (st{lastVx=jumpVx,lastNavIx=ix+1})
      
  navigateHook v = do
    warn $ "window.location assigned to `" ++ show v ++ "\' (ignoring)"
