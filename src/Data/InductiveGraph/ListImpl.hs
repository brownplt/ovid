-- |'nodeIx' is exported for the buildGraph function in ListM.
module Data.InductiveGraph.ListImpl (InductiveGraph, Node, newVertex, vertexValue, updateVertex, insertEdge, deleteEdge,
  isEdgePresent, reverseEdges, vertexSuccs, graphFold, removeToEdges, emptyGraph, nodeIx, firstVertex, 
  combineVertices, foldVerticesM) where

import Framework
import Control.Monad
import Control.Monad.State.Strict
import Data.List (partition,delete,insertBy)
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import Control.Applicative (liftA2,pure)

data Node = Node { nodeIx :: Int } deriving (Show,Ord,Eq) 

data InductiveGraph a
  = EmptyGraph
  | InductiveGraph a Node [Node] {-edges to this node from the nodes in this list-} 
      [Node] {-edges from this node to the nodes in the list-} (InductiveGraph a)
  deriving (Show)
      
------------------------------------------------------------------------------------------------------------------------
-- Utilities

-- |Returns the index of the next vertex to be inserted into a graph
nextVx :: InductiveGraph a -> Node
nextVx EmptyGraph = Node 0
nextVx (InductiveGraph _ (Node ix) _ _ _) = Node (ix+1)

-- |Inserts a vertex into an edge-list, in order
insVx :: Node -> [Node] -> [Node]
insVx vx vxs = insertWithoutDuplicatesBy (reverseCompare compare) vx vxs

-- |Merges two ordered edge-lists
mergeVxs :: [Node] -> [Node] -> [Node]
mergeVxs vxs1 vxs2 = mergeWithoutDuplicatesBy (reverseCompare compare) vxs1 vxs2

------------------------------------------------------------------------------------------------------------------------
-- Interface

emptyGraph :: InductiveGraph a
emptyGraph = EmptyGraph

firstVertex :: Node
firstVertex = nextVx EmptyGraph

newVertex :: a -> InductiveGraph a -> (InductiveGraph a,Node)
newVertex a gr = (InductiveGraph a (nextVx gr) [] [] gr, nextVx gr)

vertexValue :: Monad m => Node -> InductiveGraph a -> m a
vertexValue _ EmptyGraph = fail "vertexValue: empty graph"
vertexValue n (InductiveGraph a n' _ _ rest)
  | n > n'    = fail "vertexValue: nonexistant node"
  | n == n'   = return a
  | otherwise = vertexValue n rest

-- |Updates the value of the specified vertex.
updateVertex :: Monad m => Node -> a -> InductiveGraph a -> m (InductiveGraph a)
updateVertex _ _ EmptyGraph = fail "updateVertex: emptyGraph"
updateVertex n' a' (InductiveGraph a n to from rest)
  | n' > n    = fail "updateVertex: nonexistant node"
  | n' == n   = return (InductiveGraph a' n to from rest)
  | otherwise = updateVertex n' a' rest >>= \rest' -> return (InductiveGraph a n to from rest')

-- |Insert an edge from 'm' to 'n'.
insertEdge :: Monad m => Node -> Node -> InductiveGraph a -> m (InductiveGraph a)
insertEdge m n EmptyGraph = fail "insertEdge: vertices not found"
insertEdge m n (InductiveGraph a q to from rest)
  -- at m, and n occurs in rest since m > n. Since we are adding an edge m-->n, n gets added to the from list here
  | m >= n && m == q = return (InductiveGraph a q to (insVx n from) rest)
  -- at m, and m < n.  So, n occurs before.  We should have caught this earlier. 
  | m < n && m == q = error "insertEdge: m < n, and we are at m (implementation bug)"
  -- at n, and since m <= n, m is in rest. Since we are adding m-->n, we add m as an edge to this node.
  | m <= n && n == q = return (InductiveGraph a q (insVx m to) from rest)
  -- at n, and m > n.  So, we should have encountered m earlier.
  | m > n && n == q = error "insertEdge: m > n, and we are at n (implementation bug)"
  | otherwise =  insertEdge m n rest >>= \rest' -> return (InductiveGraph a q to from rest')


-- |Delete an edge from 'vx1' to 'vx2.'
deleteEdge :: Monad m => Node -> Node -> InductiveGraph a -> m (InductiveGraph a)
deleteEdge vx1 vx2 graph =
  let isEdgeFrom = vx1 >= vx2 -- True if the edge appears on vx1's from-list
      edge = if isEdgeFrom then vx2 else vx1
      del _    EmptyGraph = fail "deleteEdge: empty graph"
      del inVx (InductiveGraph a vx to from subgraph)
        | inVx < vx = del inVx subgraph >>= \subgraph' -> return (InductiveGraph a vx to from subgraph')
        | inVx > vx = fail "graph does not contain vx1"
        | inVx == vx && isEdgeFrom =
              if edge `elem` from 
                then return (InductiveGraph a vx to (delete edge from) subgraph)
                else fail "deleteEdge: edge not found (in from list)"
        | otherwise {- inVx == vx && not isEdgeFrom -} =
              if edge `elem` to
                then return (InductiveGraph a vx (delete edge to) from subgraph)
                else fail "deleteEdge: edge not found (in to list)"
  in if isEdgeFrom -- Is vx1 >= vx2?
       -- Is so, we will find vx1 first and the edge will be *from* vx1 to vx2
       then del vx1 graph
       -- If not, we will find vx2 first and the edge will be *to* vx2 from vx1.
       else del vx2 graph 

-- |Fails if either 'm' or 'n' does not exist
isEdgePresent :: Node -> Node -> InductiveGraph a -> Bool
isEdgePresent m n EmptyGraph = False
isEdgePresent m n (InductiveGraph a q to from rest)
  | m >= n && m == q = n `elem` from 
  | n >= m && n == q = m `elem` to
  | m > q = error ("isEdgePresent: non-existant vertex as first argument: " ++ show m)
  | n > q = error ("isEdgePresent: non-existant vertex as second argument: " ++ show n)
  | otherwise = isEdgePresent m n rest

-- |Immediate successors of this vertex.
vertexSuccs :: Node -> InductiveGraph a -> [Node]
vertexSuccs n EmptyGraph = []
vertexSuccs n (InductiveGraph _ n' to from rest)
  | n > n' = []
  | n == n' = from
  | n < n' && n `elem` to = n':(vertexSuccs n rest)
  | otherwise = vertexSuccs n rest

graphFold :: ((a,Node,[Node],[Node]) -> b -> b) -> b -> InductiveGraph a -> b
graphFold f acc EmptyGraph = acc
graphFold f acc (InductiveGraph a n to from rest) = f (a,n,to,from) (graphFold f acc rest)

 
-- |Transforms the inductive graph, turning "to-edges" into "from-edges."  This
-- breaks the inductive invariant, but is necessary to build a cyclic graph
-- structure.
removeToEdges :: InductiveGraph a -> InductiveGraph a
removeToEdges gr = remove' gr [] where
  remove' EmptyGraph [] = EmptyGraph
  remove' EmptyGraph extras = 
    error $ "InductiveGraph.ListImpl.removeToEdges : " ++ show (length extras) ++ " edges left"
  remove' (InductiveGraph a vx to from rest) es =
    let es' = map (\e -> (e,vx)) to -- edges from n' (others) to this--pass down the list
        (fromEdges,es'') = partition (\(e,_) -> e == vx) es -- accumulated list of edges from others to this
        -- edges from this node to others
        from' = map snd fromEdges 
      in InductiveGraph a vx [] (from ++ from') (remove' rest (es' ++ es''))

      
-- |Reverses the edges of the graph.
reverseEdges :: InductiveGraph a -> InductiveGraph a
reverseEdges EmptyGraph = EmptyGraph
reverseEdges graph@(InductiveGraph a vxTop toVx fromVx inner) =
  let -- vxTop is the outermost vertex.  When the graph is reversed, it will become the innermost vertex with 
      -- nodeIx = 0.
      transVx (Node ix) = Node (nodeIx vxTop - ix)
      transVxs = map transVx
      -- partitions the edge list, selecting edges from 'vx'
      partitionFromVx vx vxs = partition (\(vx',_) -> vx' == vx) vxs
      -- partitions the edge list, selecting edges to 'vx'
      partitionToVx vx vxs = partition (\(_,vx') -> vx' == vx) vxs
      makeTo vx' vxs = map (\vxTo -> (vx',transVx vxTo)) vxs
      makeFrom vx' vxs = map (\vxFrom -> (transVx vxFrom,vx')) vxs
      reverse' EmptyGraph [] [] inner = inner
      reverse' EmptyGraph tos froms _ = error $ "reverseEdges : " ++ show (length $ froms ++ tos) ++ " edges left"
      reverse' (InductiveGraph a vx toVx fromVx outer) tos froms inner =
        let vx' = transVx vx
            (toVx',otherTos) = partitionToVx vx' tos
            (fromVx',otherFroms) = partitionFromVx vx' froms
          in reverse' outer ((makeTo vx' toVx) ++ otherTos) ((makeFrom vx' fromVx) ++ otherFroms) 
               (InductiveGraph a vx' (map fst toVx') (map snd fromVx') inner)
    in reverse' graph [] [] EmptyGraph
    
{-
filterVertices :: (a -> Bool) -> InductiveGraph a -> InductiveGraph a
filterVertices f graph = filter' graph ... where
  filter' (InductiveGraph a vx toVx fromVx subgraph) | not (f a) =
    let (edges,subgraph') = filter' 
-}

foldVerticesM :: Monad m => ((a,Node,[Node],[Node]) -> b -> m b) -> b -> InductiveGraph a -> m b
foldVerticesM f acc EmptyGraph = return acc
foldVerticesM f acc (InductiveGraph a ix to from subgraph) = do 
  acc' <- f (a,ix,to,from) acc
  foldVerticesM f acc' subgraph

-- |'f' must define an equivalence relation. The resultant graph has one node in each equivalence class. Which node is
-- chosen is not defined. 'f' is applied O(|V|^2) times.
combineVertices :: (a -> a -> Bool) -> InductiveGraph a -> InductiveGraph a
combineVertices f graph =
  let -- collect :: 
      collect a repVx EmptyGraph = return ([],[],[],EmptyGraph)
      collect a repVx (InductiveGraph a' vx to from rest)
        | f a a' = do -- a' is equivalent to a, so must be filtered out
          (equiv,to',from',rest') <- collect a repVx rest
          vxMap <- get
          put (M.insert vx repVx vxMap)
          return (insVx vx equiv,mergeVxs to to',mergeVxs from from',rest')
        | otherwise = do -- we keep this vertex
          -- equivVxs are inner vertices equivalent to repVx.
          (equivVxs,innerTo,innerFrom,rest') <- collect a repVx rest
          -- Since,repVx > vx (this vertex). If from / to contains any of equivVxs, filter them out.
          let (equivTo,otherTo) = partition (\vx -> vx `elem` equivVxs) to
          let (equivFrom,otherFrom) = partition (\vx -> vx `elem` equivVxs) from
          -- If we have an edge vx --> equivTo, replace it with an edge repVx --> vx (reversed), and vice versa.
          let innerTo' = if null equivFrom then innerTo else insVx vx innerTo
          let innerFrom' = if null equivTo then innerFrom else insVx vx innerFrom
          return (equivVxs,innerTo',innerFrom',InductiveGraph a' vx otherTo otherFrom rest')
      combine EmptyGraph = return EmptyGraph
      combine (InductiveGraph a vx from to rest) = do
        -- Since we reached this node, it is the representative for its equivalence class.  Traverse rest for equivalent
        -- nodes, collect their from/to lists and merge them with ours.
        (equivs,from',to',rest') <- collect a vx rest -- nothing in rest' is equivalent to vx
        -- Recurse.
        rest'' <- combine rest' -- nodes in rest'' are not equivalent to each other
        -- filter equivalent edges out
        let filteredFrom = filter (\vx -> not (vx `elem` equivs)) from
        let filteredTo = filter (\vx -> not (vx `elem` equivs)) to
        return (InductiveGraph a vx (mergeVxs filteredFrom from') (mergeVxs filteredTo to') rest'') 
     -- After applying combine, the graph has a single representative of each equivalence class.  However, the edge
     -- lists contain edges to elements that were removed.  We have a set of the vertices that were removed.  Yay! 
      filterEquiv vxMap vx rest = case M.lookup vx vxMap of
        -- by construction, if vxRep is the representative of vx, vxRep > vx and cannot be accounted for on this vertex
        Just vxRep -> insVx vxRep rest 
        Nothing    -> vx:rest 
      filterInvalidEdges _ EmptyGraph = EmptyGraph
      filterInvalidEdges vxSet (InductiveGraph a vxRep from to rest) =
        let from' = foldr (filterEquiv vxSet) [] from
            to' = foldr (filterEquiv vxSet) [] to
          in InductiveGraph a vxRep from' to' (filterInvalidEdges vxSet rest)
      (graph',vxSet) = runState (combine graph) M.empty
      graph'' = filterInvalidEdges vxSet graph'
   in graph''
   
instance Functor InductiveGraph where
  fmap _ EmptyGraph = EmptyGraph
  fmap f (InductiveGraph a ix to from subgraph) = InductiveGraph (f a) ix to from (fmap f subgraph)

instance F.Foldable InductiveGraph where
  foldr _ b EmptyGraph = b
  foldr f b (InductiveGraph a _ _ _ subgraph) = F.foldr f (f a b) subgraph

instance T.Traversable InductiveGraph where
  traverse f EmptyGraph = pure EmptyGraph
  traverse f (InductiveGraph a ix vxTo vxFrom subgraph) = 
    liftA2 (\a' subgraph' -> InductiveGraph a' ix vxTo vxFrom subgraph') (f a) (T.traverse f subgraph)
   
------------------------------------------------------------------------------------------------------------------------
