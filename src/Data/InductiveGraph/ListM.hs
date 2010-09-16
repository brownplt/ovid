module Data.InductiveGraph.ListM (Node, GraphT, filterVertices, buildGraph, InductiveGraph, doesNodeExist,
  doesEdgeExist, firstNode, getGraph, combineNodes, buildInductiveGraph,buildGraph') where

import Control.Monad.State
import Control.Monad.Trans
import Control.Monad
import Data.List (partition,delete)
import qualified Data.Map as M
import Data.InductiveGraph.ListImpl
import Data.InductiveGraph.Class
  
type GraphT a m = StateT (M.Map a Node,InductiveGraph a) m

-- |The list-based graph implementation maintains unique node labels.
instance (Monad m, Ord a) => GraphM (GraphT a m) Node a () where
  newNode a = do
    (map,graph) <- get
    case M.lookup a map of
      Just n' -> return n'
      Nothing -> do
        let (graph',n') = newVertex a graph
        let map' = M.insert a n' map
        put (map',graph')
        return n'
        
  adjustNode a a' 
    | a /= a' = fail "updateNode: updated value must be (==)"
    | otherwise = do
      (map,graph) <- get
      case M.lookup a map of
        Just n -> do
          graph' <- updateVertex n a' graph
          put (M.insert a' n (M.delete a map),graph')
        Nothing -> fail "adjustNode could not find node"
  
  updateNode n f = do
    (map,graph) <- get
    a <- vertexValue n graph 
    adjustNode a (f a)
    
  nodeValue n = do
    (_,graph) <- get
    vertexValue n graph
            
  newEdge () m n = do
    (map,graph) <- get
    graph' <- insertEdge m n graph
    put (map,graph')
    
  removeEdge () m n = do
    (map,graph) <- get
    case deleteEdge m n graph of
      Just graph' -> put (map,graph') >> return True
      Nothing -> return False

doesNodeExist a = do
  (map,_) <- get
  return (M.member a map) 

doesEdgeExist m n = do
  (_,graph) <- get
  return (isEdgePresent m n graph)
  
  
firstNode = firstVertex

combineNodes f = do
  (_,gr) <- get
  let gr' = combineVertices f gr
  let vxMap' = graphFold (\ (a,ix,_,_) vxMap -> M.insert a ix vxMap) M.empty gr'
  put (vxMap',gr')

  
followEdges :: (Monad m, Ord a)
            => (a -> Bool)
            -> Vertex a -- ^index of a vertex that is /in/ the graph
            -> Node
            -> [Vertex a]
            -> [a] -- ^vertices that we have already dropped
            -> GraphT a m [a] -- ^return a list of dropped vertices
followEdges f vx _ [] dropped = return dropped
followEdges f vx vxix (v:vs) dropped
  | vx == v = return dropped
  | f (vxVal v) == False = do
      if (vxVal v) `elem` dropped
        then followEdges f vx vxix vs dropped
        else do dropped <- followEdges f vx vxix (vxTo v) ((vxVal v):dropped)
                followEdges f vx vxix vs dropped
  | otherwise = do
      -- if the node already exists, it won't get created
      vx' <- newNode (vxVal v)
      edgeExists <- doesEdgeExist vxix vx'
      unless edgeExists (newEdge () vxix vx')
      followEdges f vx vxix vs dropped -- since we added vx', we stop and dont follow
  
filterVertices :: (Monad m, Ord a) => (a -> Bool) -> [Vertex a] -> GraphT a m ()
filterVertices _ [] = 
  return ()
filterVertices f (v:vs) 
 | f (vxVal v) == False = filterVertices f vs
 | otherwise = do
     vx <- newNode (vxVal v)
     followEdges f v vx (vxTo v) []
     filterVertices f vs
     
getGraph :: Monad m => GraphT a m (InductiveGraph a)
getGraph = do
  (_,graph) <- get
  return graph
  
buildGraph' :: InductiveGraph a ->  [Vertex a]
buildGraph' gr =
  let gr' = removeToEdges gr
      makeVertex (a,n,[],from) rest = (Vertex (nodeIx n) a (map vRef from)):rest
      makeVertex (_,_,(_:_),_) _ =
        error "InductiveGraph.ListImpl.buildGraph' (1)"
      vRef n' = ref' vx where
                  ref' [] = 
                    error "Data.InductiveGraph.ListImpl.buildGraph' : broken"
                  ref' (v@(Vertex n _ _):vs)
                    | n == nodeIx n' = v
                    | otherwise = ref' vs
      vx  = graphFold makeVertex [] gr'
     in vx

buildInductiveGraph :: (Monad m) => GraphT a m v -> m (v,InductiveGraph a)
buildInductiveGraph buildM = do
  let buildM' = do
        v <- buildM
        graph <- getGraph
        return (v,graph)
  evalStateT buildM' (M.empty,emptyGraph)
     
buildGraph :: (Monad m) 
           => (GraphT a m) v -> m (v,[Vertex a]) 
buildGraph grM = do
  (v,(_,gr)) <- runStateT grM (M.empty,emptyGraph)
  return (v,buildGraph' gr)
  
