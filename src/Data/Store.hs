-- |Removes the social stigma of using 'IORef's.  After all, its merely mutation and has nothing to do
-- with I/O.
module Data.Store (Store) where

import Data.IORef

class (Monad m) => Store m r | m -> r where
  ref :: a -> m (r a)
  unref :: r a -> m a
  set :: r a -> a -> m ()
  update :: r a -> (a -> a) -> m ()
  
  update box f = do
    a <- unref box
    set box (f a)

instance Store IO IORef where
  ref = newIORef
  unref = readIORef
  set = writeIORef

