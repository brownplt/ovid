module Test.Data.Zipper where

import Control.Monad.Identity
import Data.Zipper

tree1 = Node 1 [Node 2 [],
                Node 3 [Node 5 []],
                Node 4 []]

tree11 = (fromLocation.up.right.down.toLocation) tree1 -- == tree1

tree12 = (fromLocation.down.right.down.toLocation) tree1 -- == Node 5 []

zt1 = do
  withCurrentChild getNode
  

zt2 :: ZipperT Int Identity Int
zt2 = do
  withCurrentChild getNode
  shiftRight
  withCurrentChild getNode

  
zt1r = runIdentity $ runZipperT zt1 (toLocation tree1)
zt2r = runIdentity $ runZipperT zt2 (toLocation tree1)
