module CFA
  ( flow1
  , flow2
  , filteredSubset
  , AbstractValue (..)
  , newCall
  , callStack
  , topContour
  , latestContext
  , Contour
  , Constraint
  , Cache
  , emptyCache
  , valuesOf
  , sourcesOf'
  , CFAState
  , CfaT
  , getContourLength
  , getCache
  , addConstraint
  , flow
  , subsetOf
  , propagate
  , propagateTo
  , removeValue
  , newValue
  , currentValues
  , uniqueLabel
  , emptyContour
  , currentSetSize
  , runCfa
  , sources
  , builtinLabel
  , extendContour
  ) where

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Reader.Class
import Data.List(find,isPrefixOf)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Data.Set as S
import Test.HUnit.Base
import Framework

import CFA.Labels (Label (..),primeLabel)
import qualified CFA.Labels as Labels

flow1 src sink f = flow [src] sink f' where
  f' [v] = f v
  f' vs = error $ "flow1:  implementation of CfaM provided " ++ show (length vs) ++ " values; expected just 1."
  
flow2 src1 src2 sink f = flow [src1,src2] sink f' where
  f' [v,w] = f v w
  f' vs = error $ "flow2:  implementation of CfaM provided " ++ show (length vs) ++ " values; expected two."


filteredSubset f src dest =
  propagateTo src dest $ \val -> 
    if f val 
      then newValue val dest 
      else return ()

-- |Without these dependencies, we have a lot of trouble in real implementations.
class (Show v, Ord v) => AbstractValue v where
  haltCycle :: Monad m => [v] -> [v] -> CfaT v m [v]

-- |The abstract type of set label
type SetLabel = (Label,Contour)

data Contour = Contour [Label] [Label]

newCall :: Label -> Contour -> Contour
newCall lbl (Contour ct lbls) = Contour ct (lbl:lbls)

callStack :: Contour -> [Label]
callStack (Contour _ lbls) = lbls

topContour :: Contour
topContour = Contour [] []

latestContext :: Contour -> Maybe Label
latestContext (Contour [] _) = Nothing
latestContext (Contour (c:_) _) = Just c
  
instance Eq Contour where
  (Contour lbls1 _) == (Contour lbls2 _) = lbls1 == lbls2
  
instance Ord Contour where
  compare (Contour lbls1 _) (Contour lbls2 _) = compare lbls1 lbls2
  
instance Show Contour where
  show (Contour lbls _) = show lbls --(map fromEnum lbls)

  
  

data Constraint v m
  = Subset (Label,Contour) (Label,Contour)
  -- |'Propagate s t f' entails that when a value, 'x $\in$ s' satisfies some
  -- predicate, 'f x' returns a computation that inserts appropriate constraints.
  | Propagate (Label,Contour) (v -> CfaT v m ())
  | PropagateTo SetLabel SetLabel (v -> CfaT v m ())
  
instance Show (Constraint v m) where
  show (Propagate from _) = "Propogate " ++ (show from)
  show (Subset f t)    = "Subset " ++ (show f) ++ " " ++ (show t)
  show (PropagateTo from to _) = 
    "Propagate from " ++ show from ++ " to " ++ show to 

instance Eq (Constraint v m) where
  (Subset s11 s12) == (Subset s21 s22) = s11 == s21 && s12 == s22
  (PropagateTo s11 s12 _) == (PropagateTo s21 s22 _) = s11 == s21 && s12 == s22
  _ == _ = False -- abuse!
  
instance Ord (Constraint v m) where
  compare (Subset s11 s12) (Subset s21 s22)
    | s11 == s21 = compare s12 s22
    | otherwise  = compare s11 s21
  compare (PropagateTo s11 s12 _) (PropagateTo s21 s22 _)
    | s11 == s21 = compare s12 s22
    | otherwise  = compare s11 s21
  compare (Propagate _ _) (Propagate _ _) = LT -- abuse!
  compare (Subset _ _) (PropagateTo _ _ _) = LT
  compare (Subset _ _) (Propagate _ _) = LT
  compare (PropagateTo _ _ _) (Propagate _ _) = LT
  compare (Propagate _ _) (PropagateTo _ _ _) = GT
  compare (Propagate _ _) (Subset _ _) = GT
  compare (PropagateTo _ _ _) (Subset _ _) = GT
  
  
-- ---------------------------------------------------------------------------------------------------------------------
-- Store manipulation

-- |A cache maps sets to sets of values and sets of sources.
type Cache v = Map Label (Map Contour (Set v,Set (Label,Contour)))

emptyCache :: Cache v
emptyCache = M.empty

valuesOf :: AbstractValue v => (Cache v) -> (Label,Contour) -> [v]
valuesOf cache (lbl,ct) = case M.lookup lbl cache of
  Just ctCache -> case M.lookup ct ctCache of
    Just (valSet,_) -> S.toList valSet
    Nothing -> []
  Nothing -> []

sourcesOf' cache (lbl,ct) = case M.lookup lbl cache of
  Just ctCache -> case M.lookup ct ctCache of
    Just (_,srcSet) -> srcSet
    Nothing -> S.empty
  Nothing -> S.empty

-- ---------------------------------------------------------------------------------------------------------------------


type Constraints v m = Map (Label,Contour) (Set (Constraint v m))
  
data CFAState v m = CFAState {
  contourLength :: Int,
  cache         :: Cache v,
  constraints   :: Constraints v m,
  nextLabel     :: Int
}

-- The internal counter is for labelling.
type CfaT v m a = StateT (CFAState v m) m a

-------------------------------------------------------------------------------

getContourLength :: (Monad m, AbstractValue v) => CfaT v m Int
getContourLength = get >>= (return.contourLength)

getCache :: (Monad m, AbstractValue v) => CfaT v m (Cache v)
getCache = get >>= (return.cache)

getConstraints :: (Monad m, AbstractValue v) => CfaT v m (Constraints v m) 
getConstraints = get >>= (return.constraints)

putCache s = do
  cfa <- get
  put $ cfa { cache = s }

putConstraints c = do
  cfa <- get
  put $ cfa { constraints = c }

interpretConstraint :: (MonadIO m, AbstractValue v) => v -> Constraint v m
                    -> CfaT v m ()
interpretConstraint val (Propagate _ f) = f val
interpretConstraint val (PropagateTo src dest f) = f val
interpretConstraint val (Subset _ t)      = newValue val t

addConstraint :: (Monad m, AbstractValue v) => Constraint v m -> SetLabel
              -> CfaT v m Bool
addConstraint c sv = do
  constraints <- getConstraints
  case M.lookup sv constraints of
    Nothing -> do
      putConstraints $ M.insert sv (S.singleton c) constraints
      return True
    Just set ->
      if S.member c set
        then return False
        else do putConstraints $ M.insert sv (S.insert c set) constraints
                return True

applyConstraintTo :: (MonadIO m, AbstractValue v) => Constraint v m -> SetLabel
                  -> CfaT v m ()
applyConstraintTo c set = do
  cache <- getCache
  mapM_ (\val -> interpretConstraint val c) (valuesOf cache set)

-- |Adding an edge from 'src' to 'sink' in the transitive closure of the dataflow graph.  We have a cycle if there is an
-- edge from 'sink' to 'src in the transitive closure of the dataflow grpah
addFlow :: (MonadIO m, AbstractValue v) => (Label,Contour) -> (Label,Contour) -> CfaT v m Bool
addFlow src sink | src == sink = return True
addFlow src sink@(sinkLbl,sinkCt) = do
  cache <- getCache
  if sink `S.member` (sourcesOf' cache src) -- sourcesOf' tells us which nodes have edges to us
    then return False
    else do case M.lookup sinkLbl cache of
              Just ctCache -> case M.lookup sinkCt ctCache of
                Just (_,srcs) ->
                  putCache $ M.insert sinkLbl (M.adjust (\(vals,srcs) -> (vals,S.insert src srcs)) sinkCt ctCache) cache
                Nothing -> 
                  putCache $ M.adjust (\ctCache -> M.insert sinkCt (S.empty,S.singleton src) ctCache) sinkLbl cache
              Nothing ->
                putCache $ M.insert sinkLbl (M.singleton sinkCt (S.empty,S.singleton src)) cache
            -- warn $ "added flow from " ++ show src ++ " to " ++ show sink
            return True

getFlows :: (Monad m, AbstractValue v)
         => (Label,Contour) -> CfaT v m [(Label,Contour)]
getFlows set = do
  cache <- getCache
  return $ S.toList (sourcesOf' cache set) 

sources :: (Monad m, AbstractValue v)
        => (Label,Contour) -> CfaT v m [(Label,Contour)]
sources = getFlows

pairWith :: (a -> b -> c) -> [a] -> [b] -> [c]
pairWith f _ [] = []
pairWith f [] _ = []
pairWith f (a:as) bs = (map (f a) bs) ++ (pairWith f as bs)
  
pairwiseFlatten :: [[a]] -> [[a]]
pairwiseFlatten [] = []
pairwiseFlatten (xs:xss) = pairWith (:) xs (pairwiseFlatten xss)
  

flow [] _ _ = fail "flow: expected at least one source"
{-  flow [src] sink f = propagateTo src sink $ \val -> case f [val] of -- special case for clarity / efficiency
  Just val' -> newValue val' sink
  Nothing -> return () -}
flow srcs sink f = do
  let addFlows [] = return True 
      addFlows (src:srcs) = do
        canFlow <- addFlow src sink
        case canFlow of
          True -> addFlows srcs
          False -> do
            addFlows srcs
            return False
  srcSrcs <- mapM getFlows srcs
  isNotCycle <- addFlows (srcs ++ concat srcSrcs)
  case isNotCycle of
    True -> (foldl flow' base srcs) [] where
              base vs = case f vs of -- it's crucial that base receives all values.
                Just v -> newValue v sink
                Nothing -> return ()
              flow' f src vs = propagateTo src sink (\v -> f (v:vs))
    False -> do
      srcValss <- mapM currentValues srcs
      let newVals = catMaybes $ map f (pairwiseFlatten srcValss)
      existingVals <- currentValues sink
      genericVals <- haltCycle newVals existingVals
      mapM_ (\val -> newValue val sink) genericVals                  

subsetOf subset superset = do
  let addFlows [] = return True 
      addFlows (src:srcs) = do
        canFlow <- addFlow src superset
        case canFlow of
          True -> addFlows srcs
          False -> do
            addFlows srcs -- add the rest, but report a cycle 
            return False
  srcSrcs <- getFlows subset
  isNotCycle <- addFlows (subset:srcSrcs)
  case isNotCycle of
    True -> do
     addConstraint (Subset subset superset) subset
     applyConstraintTo (Subset subset superset) subset
    False -> do
      newVals <- currentValues subset
      existingVals <- currentValues superset
      genericVals <- haltCycle newVals existingVals
      mapM_ (\val -> newValue val superset) genericVals
      
propagate set f = do
  addConstraint (Propagate set f) set
  applyConstraintTo (Propagate set f) set

propagateTo from to f = do
  isNew <- addConstraint (PropagateTo from to f) from
  when isNew (applyConstraintTo (PropagateTo from to f) from)
        
removeValue v set@(lbl,ct) = do
  cache <- getCache
  case M.lookup lbl cache of
    Nothing -> return ()
    Just ctCache -> case M.lookup ct ctCache of
      Nothing -> return ()
      Just (vals,_) -> 
        putCache $ M.insert lbl (M.adjust (\(vals,srcs) -> (S.delete v vals,srcs)) ct ctCache) cache
 
clearValues set@(lbl,ct) = do
  cache <- getCache
  case M.lookup lbl cache of
    Nothing -> return ()
    Just ctCache -> case M.lookup ct ctCache of
      Nothing -> return ()
      Just (vals,_) -> 
        putCache $ M.insert lbl (M.adjust (\(_,srcs) -> (S.empty,srcs)) ct ctCache) cache

newValue v set@(lbl,ct) = do
  cache <- getCache
  cs <- getConstraints
  case M.lookup lbl cache of
    Nothing -> do
      -- Create a new set, so run any existing constraints on v
      putCache $ M.insert lbl (M.singleton ct (S.singleton v,S.empty)) cache
      mapM_ (interpretConstraint v) 
            (S.toList $ M.findWithDefault S.empty set cs)
    Just ctCache -> do
      case M.lookup ct ctCache of
        Nothing -> do
          -- Create a new set, so run any existing constraints on v
          putCache $ M.insert lbl (M.insert ct (S.singleton v,S.empty) ctCache) cache
          mapM_ (interpretConstraint v) 
                 (S.toList $ M.findWithDefault S.empty set cs)
        Just (vals,_) | S.size vals == 40 ->
           warn $ "large set: " ++ show lbl
                      | otherwise -> do
          -- The set exists, so if v is already in the set, we don't need to
          -- run existing constraints on it.
          unless (S.member v vals) $ do
            putCache $ M.insert lbl (M.adjust (\(vals,srcs) -> (S.insert v vals,srcs)) ct ctCache) cache
            mapM_ (interpretConstraint v)
                  (S.toList $ M.findWithDefault S.empty set cs)

currentValues set = do
  cache <- getCache
  return (valuesOf cache set)

uniqueLabel :: (Monad m, AbstractValue v)
            => CfaT v m Label  
uniqueLabel = do
  st@(CFAState{nextLabel=next}) <- get
  put (st{nextLabel=next+1})
  return (IxLabel next)

builtinLabel id = do
  st@(CFAState{nextLabel=next}) <- get
  put (st{nextLabel=next+1})
  return (SourceLabel Nothing (Just id) next)


extendContour label ct@(Contour labels v) = do
  n <- getContourLength
  let ct' = take n (label:labels)
  return (Contour ct' v)


-- Hack to avoid a combinatorial explosion when dealing with singly-recursive
-- functions that have multiple points where recursive calls are made.
{- This screws up the CFG
extendContour label ct@(Contour labels v)
 | label `elem` labels = return ct
 | otherwise = do n <- getContourLength
                  return (Contour (take n (label:labels)) v)
-}

emptyContour :: (Monad m,AbstractValue v) => CfaT v m Contour
emptyContour = return topContour

currentSetSize (lbl,ct) = do
  cache <- getCache
  case M.lookup lbl cache of
    Just ctCache -> case M.lookup ct ctCache of
      Just (vals,_) -> return (S.size vals)
      Nothing -> return 0
    Nothing -> return 0

      
runCfa :: (Monad m, Ord v) => Int -> Int -> CfaT v m a
       -> m (a,Cache v, Constraints v m)
runCfa contourLength initLabel cfaM = do
  (a,cfa) <- runStateT cfaM (CFAState contourLength M.empty M.empty initLabel)
  return (a,cache cfa, constraints cfa)

