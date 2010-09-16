module Data.InductiveGraph.Class 
  ( GraphM (..)
  , Vertex (..)
  , expandedVertexShow
  , graphToEdgeList
  , verticesToMzSchemeReadable
  ) where

import Data.List (intersperse)

class Monad m => GraphM m n a e | m -> n, m -> a, m -> e where
  newNode :: a -> m n 
  adjustNode :: a -> a -> m ()
  updateNode :: n -> (a -> a) -> m ()
  nodeValue :: n -> m a
  newEdge :: e -> n -> n -> m ()
  -- |'False' if the edge was not found
  removeEdge :: Monad m => e -> n -> n -> m Bool
  
  
data Vertex a = Vertex 
  { vxIx  :: Int
  , vxVal :: a
  , vxTo  :: [Vertex a] }
  
findVertices :: (a -> Bool) -> [Vertex a] -> [Vertex a]
findVertices f [] = []
findVertices f (x:xs) 
  | f (vxVal x) = x:(findVertices f xs)
  | otherwise = findVertices f xs

instance Eq a => Eq (Vertex a) where
  (Vertex n1 a1 _) == (Vertex n2 a2 _) = n1 == n2 && a1 == a2 

-- | Non-terminating when the graph has cycles
expandedVertexShow :: Show a => Vertex a -> String
expandedVertexShow (Vertex n a vxs)
  = "(Vertex " ++ show n ++ " " ++ show a ++ 
      (concatMap expandedVertexShow vxs) ++ ")"

-- | 'vxs' must be a complete list of vertices.
graphToEdgeList :: [Vertex a] -> [(Int,Int)]
graphToEdgeList vxs = foldr mk [] vxs where 
  -- Adds edges from n to its neighbors and recurses on all reachable
  -- vertices.
  mk (Vertex n _ vxs') edges = foldr (newEdge n)  edges vxs'  
  -- adds the edge (n,n') to edges if it doesn't exist
  newEdge n (Vertex n' _ _) edges
    | (n,n') `elem` edges = edges
    | otherwise           = (n,n'):edges
    
    
verticesToMzSchemeReadable :: Show a => [Vertex a] -> String
verticesToMzSchemeReadable vs = 
  "(letrec (" ++ concat bindings ++ ")\n  (list" ++ concat ref  ++ "))\n" where
    (bindings,ref) = unzip (map print vs)
    print (Vertex n a ws) =
      ("[node" ++ show n ++ " (cons " ++ show a ++ 
       " (delay (list" ++ concatMap printEdge ws ++ ")))]\n"," node" ++ show n)
    printEdge (Vertex n _ _) = " node" ++ show n
