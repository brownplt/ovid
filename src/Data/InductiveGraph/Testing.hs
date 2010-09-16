module Data.InductiveGraph.Testing (hasVx, hasEdge, hasNotEdge, testGraph, numVxs, combineNodes, getGraph,
  module Data.InductiveGraph.Class, lift) where

import Test.HUnit.Base hiding (Node)
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad
import Data.InductiveGraph.Class
import Data.InductiveGraph.ListM

hasVx :: (Show vx, Ord vx)
      => vx -> (GraphT vx IO) ()
hasVx vx = do
  test <- doesNodeExist vx 
  lift $ assertBool ("expected node " ++ show vx) test
  
numVxs :: (Show vx, Ord vx) => Int -> (GraphT vx IO) ()
numVxs count = do
  (vxMap,_) <- get
  lift $ assertEqual "number of vertices" (M.size vxMap) count 
  
hasNotEdge :: (Show vx, Ord vx)
        => Node -> Node -> (GraphT vx IO) ()
hasNotEdge vx1 vx2 = do
  test <- doesEdgeExist vx1 vx2
  lift $ assertBool ("unxpected edge " ++ show vx1 ++ " " ++ show vx2) (not test)

  
hasEdge :: (Show vx, Ord vx)
        => Node -> Node -> (GraphT vx IO) ()
hasEdge vx1 vx2 = do
  test <- doesEdgeExist vx1 vx2
  lift $ assertBool ("expected edge " ++ show vx1 ++ " " ++ show vx2) test

testGraph :: (Show vx, Ord vx)
          => String
          -> ((GraphT vx IO) ())
          -> Test
testGraph msg gr = TestLabel msg $ TestCase $ do
  ((),vxs) <- buildGraph gr
  return ()

