module Ovid.ConstraintUtils where

import qualified Data.Map as M
import qualified Data.Foldable as F
import Data.Maybe
import CFA.Labels
import CFA
import Ovid.Prelude
import Ovid.Abstraction

-- #define VERBOSE_WARNINGS

addGlobals :: (MonadTrans t, Monad (t m), MonadState (JsCFAState ct) m)
           => [Label] -> t m ()
addGlobals lbls = do
  globals <- getGlobals
  setGlobals (lbls ++ globals)
  
getGlobals :: (MonadTrans t, Monad (t m), MonadState (JsCFAState ct) m)
           => t m [Label]
getGlobals = do
  JsCFAState{jscfaGlobals=globals} <- lift get
  return globals
  
setGlobals :: (MonadTrans t, Monad (t m), MonadState (JsCFAState ct) m)
           => [Label] -> t m ()
setGlobals lbls = do
  st <- lift get
  lift $ put st{jscfaGlobals = lbls}


updateCfaOpts f st = st { jscfaOpts = f (jscfaOpts st) }

getMarkedFunctions :: (MonadTrans t, Monad m, Monad (t m), MonadState (JsCFAState Contour) m) => t m [(Label,Contour)]
getMarkedFunctions = do
  st@(JsCFAState{jscfaFns=fns}) <- lift get
  return fns

markFunctionSet set = do
  st@(JsCFAState{jscfaFns=fns}) <- lift get
  lift $ put (st{jscfaFns=set:fns}) 

getMarkedBranches :: (MonadTrans t, Monad m, Monad (t m), MonadState (JsCFAState Contour) m) => t m [(Label,Contour)]
getMarkedBranches = do
  st@(JsCFAState{jscfaBranches=branches}) <- lift get
  return branches

markBranch set = do
  st@(JsCFAState{jscfaBranches=branches}) <- lift get
  lift $ put (st{jscfaBranches=set:branches}) 

  
emptyJsCFAState :: JsCFAState ct
emptyJsCFAState  = JsCFAState Nothing M.empty [] [] emptyCFAOpts []

allProperties val f = case objectProperties val of
  Nothing -> warn $ "all-properties: not an object: " ++ show val
  Just s  -> propagate s $ \pair -> case pair of
    AProperty id (ValueSet valSet) -> propagate valSet $ \val -> f id val
    otherwise -> 
      warn $ "allProperties: non-property value in property set: " ++ show pair

unsafePropagatePropertySet :: (MonadIO m)
                     => (Label,Contour) -- ^ the object set
                     -> ((Label,Contour) -> CfaT Value m ())
                     -> CfaT Value m ()
unsafePropagatePropertySet obj f = propagate obj $ \val -> case objectProperties val of
  Just propSet -> f propSet
  Nothing -> unless (val == NullVal) $ 
    warn ("propagatePropertySet: non-object value from " ++ show obj ++ "; the value is " ++ show val)
      
propagatePropertySetTo obj cxt f = propagateTo obj cxt $ \val -> case objectProperties val of
  Just propSet -> f propSet
  Nothing | val == NullVal -> return ()
          | otherwise -> warn $ "propagatePropertySetTo: non-object value from " ++ show obj 
                                 ++ "; the value is " ++ show val
    
propagatePropertyOf :: (MonadIO m)
                    => Value -- ^ the object set
                    -> (Label,Contour) -- ^source label if the property is 
                                       -- created here
                    -> String     -- ^ the name of the property
                    -> ((Label,Contour) -> CfaT Value m ()) -- ^ function applied to the value set of the property
                    -> CfaT Value m ()
propagatePropertyOf objVal cxt propId f = case objectProperties objVal of
  Just propSet -> do
    newValue (AProperty propId (ValueSet (propLabel (fst cxt) propId,snd cxt))) propSet -- create the property
    propagate propSet $ \property -> case property of
      AProperty propId' (ValueSet valSet) -> case propId' == propId of
        True -> do
          size <- currentSetSize valSet
          when (size == 0) (newValue UndefinedVal valSet) -- stupid, stupid semantics
          when (isServerVal objVal) $ do
            let (lbl,ct) = aServerValProps objVal
            lbl' <- uniqueLabel
            let svrSet = (lbl',ct)
            newValue (AServerVal svrSet) valSet
          f valSet
        False -> return ()
      otherwise -> do
        warn $ "--- ERROR ---"
        warn $ "propagateProperty: non-property value in a property at: " ++ show cxt
        warn $ "The property id is " ++ show propId
        warn $ "Value is: " ++ show property
        srcs <- sources propSet
        warn $ "Sources are:"
        warn $ show srcs
        fail "--- ERROR ---"
        return ()
  Nothing | objVal == NullVal -> return ()
          | otherwise -> do
     -- this branch will be removed once all values are objects
    return ()
    
unsafePropagateProperty obj cxt propId f = propagate obj $ \val -> propagatePropertyOf val cxt propId f

propagateProperty obj cxt propId f = propagateTo obj cxt $ \val -> propagatePropertyOf val cxt propId f

flowProperty obj propId cxt = propagateProperty obj cxt propId $ \propSet -> do 
  subsetOf propSet cxt
  

primeSet (lbl,ct) n = (primeLabel lbl n,ct) 

propagatePropertyValue :: (MonadIO m)
                       => (Label,Contour) -- ^ the object set
                       -> (Label,Contour) -- ^ source label if the property is created here
                       -> String     -- ^ the name of the property
                       -> (Value -> CfaT Value m ()) -- ^ function applied to the values of the property
                       -> CfaT Value m ()
propagatePropertyValue obj cxt id f = propagateProperty obj cxt id $ \valSet -> propagate valSet f
      
unsafePropagatePropertyValue obj cxt id f = unsafePropagateProperty obj cxt id $ \valSet -> propagate valSet f


-- |Create a new object, insert it into 'cxt' and return the object.  Uses 'primeLabel cxt 1'
newObject cxt properties = do
  prototype <- builtinPrototype "Object"
  let propSet = primeSet cxt 1
  subsetOf prototype propSet
  let insertProperty (propId,valSet) = do
        flow1 valSet propSet (\_ -> Just $ AProperty propId (ValueSet valSet))
  mapM_ insertProperty properties
  let obj = (AObject (fst cxt) propSet PNotSpecial)
  newValue (AObject (fst cxt) propSet PNotSpecial) cxt
  return obj
  
builtinPrototype obj = do
  JsCFAState {jscfasBuiltins=builtins} <- lift get
  case M.lookup (obj ++ "-props") builtins of -- clearly not hygienic
    Just lbl -> do
      ct <- emptyContour
      return (lbl,ct)
    Nothing -> fail $ "builtinPrototype: `" ++ obj ++ "' is not a builtin prototype"
  
-- |Uses 'primeLabel cxt 1' and primes them too
-- newArray :: (MonadTrans t1, MonadState (JsCFAState t) m, CfaM (t1 m) ct (Value ct)) 
--          => (Label, ct) -> [(Label, ct)] -> t1 m (Value ct)
newArray cxt items = do
  let itemSet = primeSet cxt 1
  let mkIxSet (ixSet,ix) = do
        let valSet = primeSet itemSet ix
        subsetOf ixSet valSet
        flow1 valSet itemSet (\_ -> Just $ AProperty (show ix) (ValueSet valSet))
  mapM_ mkIxSet (zip items [0..])
  -- Copy protoype methods over
  proto <- builtinPrototype "Array"
  subsetOf proto itemSet
  let arr =  (AObject (fst cxt) itemSet PArray) 
  newValue arr cxt
  return arr
  
-- newString :: (MonadTrans t1, MonadState (JsCFAState t) m, CfaM (t1 m) ct (Value ct)) 
--          => (Label, ct) -> StringPat -> t1 m (Value ct)
newString (lbl,ct) sp = do
  -- lbl' <- uniqueLabel lbl
  -- let fields = (lbl',ct)
  prototype <- builtinPrototype "String"
  -- subsetOf prototype fields
  let str = AObject lbl prototype (PString sp)
  newValue str (lbl,ct)
  return str
