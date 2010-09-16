module Ovid.Randomization where

import Ovid.Prelude
import WebBits.JavaScript.JavaScript
import Data.InductiveGraph.Class
import Data.InductiveGraph.ListImpl
import Data.InductiveGraph.ListM
import Ovid.GraphNode
import CFA.Labels
import CFA.Class


vxFilter vx = not (isJoinNode vx || isExitNode vx || isInternalNode vx)

callPos :: Memento ct => GraphNode ct -> Maybe SourcePos
callPos vx = do
  (called,ct) <- nodeSet vx
  calling <- latestContext ct
  case labelPos calling of
    Nothing -> do -- the calling function is a builtin
      pos <- labelPos called
      when (sourceName pos == "../flapjax/flapjax.js")
        (fail "built-in calling an internal")
      return pos
    Just callingPos | sourceName callingPos == "../flapjax/flapjax.js" -> labelPos called
                    | otherwise -> return callingPos

printStmt _ (Nothing,_,_,_) () = return ()
printStmt stmts (Just pos,_,_,_) () = do
  let ss = expressionsAt pos stmts
  liftIO $ putStrLn $ show (length ss) ++ " statements here!"
  liftIO $ putStrLn (show ss)
  
                    
randomizationInfo :: (MonadIO m, Ord ct,Memento ct)
                  => InductiveGraph (GraphNode ct) -> [Statement SourcePos] -> m [Vertex (GraphNode ct)] 
randomizationInfo cfg stmts = do
  (_,rev) <- buildInductiveGraph (filterVertices vxFilter $ buildGraph' (reverseEdges cfg)) 
  -- (combineVertices isEquivalentCall cfg))
  let lbls = fmap callPos rev 
  foldVerticesM (printStmt stmts) () lbls
  return (buildGraph' rev)
