-- | Defines commonly used datatypes and functions.
module Framework (
  -- * Generic Functions
    ym,ltraverse, insertRev, reverseCompare, mergeWithoutDuplicatesBy, insertWithoutDuplicatesBy
  -- * Identifiers
  -- * Pretty-Printing
  , PrettyPrintable(..)
  -- * Counters
  , UniqueM (..) -- because Data.Unique blows
  , Counter
  , CounterT
  , CounterM
  , evalCounter
  , evalCounterM
  , runCounter
  , counterInit
  -- Generics for SourcePos (instances only)
  -- type system hacks
  , EqualOrd (..)
  , eovUpd
  , warn
  -- strings
  , toLower, lowercase
  , catMaybes
  , Map
  ) where

import Data.Map (Map)
import Data.Maybe (catMaybes)
import Data.Char (toLower)
import Control.Applicative
import qualified System.IO as IO
import Control.Monad.State.Strict
import Control.Monad.Identity
import qualified Data.List as L
import Data.Generics hiding (GT)
import qualified Data.Foldable as Foldable
import Data.Foldable (Foldable)
import qualified Data.Traversable as Traversable
import Data.Traversable (Traversable, traverse)
import qualified Text.PrettyPrint.HughesPJ as Pp
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos)
import WebBits.Common

lowercase = map toLower

--------------------------------------------------------------------------------
-- Generic functions

-- |Insert into a sorted list, with the greatest element at the head.
insertRev :: (Ord a) => a -> [a] -> [a]
insertRev x xs = L.insertBy (reverseCompare compare) x xs

reverseCompare :: (a -> a -> Ordering) -> (a -> a -> Ordering)
reverseCompare f x y = case f x y of
  EQ -> EQ
  LT -> GT
  GT -> LT

mergeWithoutDuplicatesBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeWithoutDuplicatesBy f xs [] = xs
mergeWithoutDuplicatesBy f [] ys = ys
mergeWithoutDuplicatesBy f (x:xs) (y:ys) = case f x y of
  LT -> x : (mergeWithoutDuplicatesBy f xs (y:ys))
  GT -> y : (mergeWithoutDuplicatesBy f (x:xs) ys)
  EQ -> x : (mergeWithoutDuplicatesBy f xs ys)
  
insertWithoutDuplicatesBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertWithoutDuplicatesBy _ y [] = [y]
insertWithoutDuplicatesBy f y (x:xs) = case f y x of
  LT -> y:x:xs
  GT -> x:(insertWithoutDuplicatesBy f y xs)
  EQ -> x:xs
  
-- | Given an applicative functor, 'f', and and a list of traversable
-- data-structures, apply the functor to every element of the list from left
-- to right.
ltraverse:: (Traversable t, Applicative f) => (a -> f b) -> [t a] -> f [t b]
ltraverse f [] = pure []
ltraverse f (x:xs) = pure (:) <*> (traverse f x) <*> ltraverse f xs

-- | Lifts a monadic function to 'f' over 'Maybe.'
ym:: (Monad m) => (a -> m b) -> (Maybe a -> m (Maybe b))
ym _ Nothing  = return Nothing
ym f (Just a) = f a >>= return.Just


--------------------------------------------------------------------------------
-- Counter monads

class Monad m => UniqueM m where
  getCounter :: m Int
  putCounter :: Int -> m ()
  preincrCounter :: m Int

newtype Counter = Counter Int

--- |'CounterT' implements a counter and encapsulates another monad.
type CounterT m = StateT Counter m
type CounterM = CounterT Identity

counterInit = Counter 0

instance (Monad m) => UniqueM (CounterT m) where
  getCounter = do
    (Counter n) <- get
    return n
  
  preincrCounter = do
    (Counter n) <- get
    put (Counter (n+1))
    return n
  
  putCounter n = do
    put (Counter n)
  

evalCounter :: Monad m => CounterT m a -> m a
evalCounter m = evalStateT m (Counter 0)

runCounter :: Monad m => Counter -> CounterT m a -> m (a,Counter)
runCounter init m = runStateT m init


evalCounterM :: CounterM a -> a 
evalCounterM m = runIdentity $ evalCounter m

--------------------------------------------------------------------------------
-- Generics for SourcePos

-- | These definitions allow us to use data structures containing 'SourcePos'
-- values with generics.

instance Typeable (EqualOrd a) where
  typeOf _  = 
    mkTyConApp (mkTyCon "EqualOrd") []
    
-- Guesswork.  It works for Test.JavascriptParser.
equalOrdDatatype = mkDataType "EqualOrd" [equalOrdConstr1]
equalOrdConstr1 = mkConstr equalOrdDatatype "EqualOrd" [] Prefix

-- | This definition is incomplete.
instance Data (EqualOrd a) where
  -- We treat source locations as opaque.  After all, we don't have access to
  -- the constructor.
  gfoldl k z pos = z pos
  toConstr _ = equalOrdConstr1
  gunfold   = error "gunfold is not defined for EqualOrd"
  dataTypeOf = error "dataTypeOf is not defined for EqualOrd"

  
-- -----------------------------------------------------------------------------
-- EqualOrd
  
-- |A container type with instances of 'Eq' and 'Ord' defined so that all values
-- values are equal.  Hacking around equality seems a little dicey.  Use this
-- carefully.  'EqualOrd' is an instance of 'Show' as well for convenience.
data EqualOrd v = EqualOrd { equalOrdValue :: v }

instance Eq (EqualOrd v) where
  _ == _ = True
  
instance Ord (EqualOrd v) where
  compare _ _ = EQ

-- |If we allow overlapping instances, we could do a little better.
instance Show (EqualOrd v) where
  show (EqualOrd v) = "EqualOrd-value"

eovUpd :: (a -> a) -> EqualOrd a -> EqualOrd a
eovUpd f (EqualOrd x) = EqualOrd (f x)

-- ---------------------------------------------------------------------------------------------------------------------
-- Debugging

warn :: MonadIO m => String -> m ()
warn s = liftIO (IO.hPutStrLn IO.stderr s)

