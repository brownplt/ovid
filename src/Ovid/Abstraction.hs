-- |Abstract Javascript values and helpful functions.
module Ovid.Abstraction (Value (..), ValueSet (..), RawValue (..), CEnv, functionLabel, objectProperties, isBuiltin,
  hasProperties, flattenValue, PrimObject (..), isAbstractArray, StringPat(..), unStringPat, stringPatCat,
  unStringPatForOnDemandJavaScript, isServerVal,justProperty,asPropId, closureThis, isFalseValue,isTrueValue,
  isUndefinedValue) where

import Ovid.Prelude
import qualified Data.Map as M
import CFA.Labels (Label,unsafeLabelIx)
import CFA
import qualified WebBits.JavaScript.JavaScript as Js
import Ovid.Environment (Ann)


type Statement = Js.Statement Ann
type CEnv c = M.Map Label c

flattenValue :: (Cache Value) -> Value -> RawValue
flattenValue r v = absValue v where
  absProp (AProperty id (ValueSet set)) = Just (id,map absValue (valuesOf r set))
  absProp _ = Nothing
  absValue (AObject{aObjectProps=propSet,aObjectX=x}) = VObject (catMaybes $ map absProp (valuesOf r propSet)) x
  absValue (AServerVal (lbl,ct)) = case unsafeLabelIx lbl of
    Just ix -> VServer ix
    Nothing -> error "wrong kind of label, omg"
  absValue _ = VUnknown

data RawValue
  = VObject {
      vObjectMap :: [(String,[RawValue])], vObjectX :: PrimObject Contour
    }
  | VServer Int
  | VUnknown
  | VAtom Value
  deriving (Show)

instance Write RawValue where
  write (VObject kvs PNotSpecial) = 
    "#(" ++ concat (map write kvs) ++ ")"
  write (VObject _ (PString sp)) = write sp
  write (VObject kvs PArray) = write (catMaybes $ map write' kvs) where
    write' (id,vs) = case tryInt id of
      Nothing -> Nothing
      Just ix -> Just vs
  write (VServer ix) = "(server " ++ show ix ++ ")" 
  write VUnknown = "unknown"
  write (VAtom v) = write v

instance Write Value where
  write AnyNum = "number"
  write AnyBool = "boolean"
  write AnyRegexp = "regexp"
  write NullVal = "null"
  write UndefinedVal = "undefined"
  write (ANum v) = write v
  write (ABool v) = write v
  write other  = "(atom " ++ show other ++ ")"
  
instance Show Value where
  show AnyNum = "[number]"
  show AnyBool = "[bool]"
  show AnyRegexp = "[regexp]"
  show NullVal = "null"
  show UndefinedVal = "undefined"
  show (ANum n) = show n
  show (ABool b) = show b
  show (ARegexp s _ _) = "/" ++ s ++ "/"
  show (AFunction lbl args locals _ env props this) = 
    "[function:" ++ show lbl ++ "," ++ show props ++ "]"
  show (ABuiltin{aBuiltinLabel=lbl}) = "[builtin:" ++ show lbl ++ "]"
  show (AProperty id _) = "." ++ id
  show (AServerVal _) = "[from-server]"
  show (AObject _ _ (PString sp)) = show (unStringPatForOnDemandJavaScript sp)
  show (AObject _ _ PFunction{}) = error "PFunctions not used yet"
  show (AObject lbl _ PArray) = "[array:" ++ show lbl ++ "]"
  show (AObject lbl _ PNotSpecial) = "[object:" ++ show lbl ++ "]"
  
data Value
  -- Atomic values
  = AnyNum | AnyBool | AnyRegexp | NullVal | UndefinedVal 
  | ANum Double | ABool Bool | ARegexp String Bool Bool
  -- | When we apply a function, we map local identifiers to the dynamic
  -- contour in the CEnv, the same way we handle arguments.
  | AFunction {
      aFunctionLabel  :: Label,
      aFunctionArgs   :: [Label],
      aFunctionLocals :: [Label],
      aFunctionBody   :: (EqualOrd Statement),
      aFunctionEnv    :: CEnv Contour,
      aFunctionProps  :: (Label,Contour),
      aFunctionThis   :: Label
    }
  | ABuiltin {
      aBuiltinName  :: String,
      aBuiltinLabel :: Label,
      aBuiltinThis  :: Label,
      aBuiltinProps :: Maybe Label
    }
  | AProperty {
      aPropertyId   :: String,
      aPropertyVals :: ValueSet Contour
    }
  -- | We care about the contours of method calls.  Therefore, every object
  -- specifies the contour in which it was created.  Therefore, when applying
  -- an object's (obj's) method, we label the actuals with the contour of obj.
  | AObject {
      aObjectLabel :: Label, -- ^source label where this object was created
      aObjectProps :: (Label,Contour),
      aObjectX :: PrimObject Contour
    }
  -- |Represents a value returned by the server (i.e. as a response to an XMLHttpRequest. We don't know what this
  -- value is, but we can infer its structure (as a object) based on how its used. In particular, its label is its
  -- identity as a server-value and references its property set, when we are able to infer that it is an object.
  | AServerVal {
      aServerValProps :: (Label,Contour)
    }
  deriving (Eq,Ord)
  
-- |Additional information to precisely model certain primitive objects, such as strings and arrays.
data PrimObject ct 
  = PNotSpecial  -- ^avoid 'Maybe'-pollution
  | PArray -- ^arrays require special treatment in iterators
  | PString StringPat -- ^string objects work with the (+) operator
  | PFunction {
      pFunctionArgs   :: [Label], -- ^formals
      pFunctionLocals :: [Label], -- ^locals
      pFunctionBody   :: (EqualOrd Statement), -- ^definition
      pFunctionEnv    :: CEnv ct, -- ^environment
      pFunctionThis   :: Label -- ^formal label of the this parameter
    }
  deriving (Eq,Ord,Show)
  
-- ---------------------------------------------------------------------------------------------------------------------
-- String abstractions
  
data StringPat = SConst String 
               | SCat StringPat StringPat
               | SAny deriving (Eq,Ord,Show)

instance Write StringPat where
  write (SConst s) = write s
  write (SCat x y) = "(cat " ++ write x ++ " " ++ write y ++ ")"
  write SAny = "string"

-- |Converts a 'StringPat' to a 'String', if the abstraction represents a fixed string.
unStringPat :: StringPat -> Maybe String
unStringPat (SConst s) = Just s
unStringPat _ = Nothing

stringPatCat :: StringPat -> StringPat -> StringPat
stringPatCat (SConst s1) (SConst s2) = SConst (s1 ++ s2)
stringPatCat SAny SAny = SAny
stringPatCat x y = SCat x y

-- |Converts a 'StringPat' into a 'String' containing HTML.  This is required to handle absurd (and insecure) uses
-- of .innerHHTML and ``on demand'' JavaScript.  As a first approximation, we replace all 'SAny' with "".
unStringPatForOnDemandJavaScript :: StringPat -> String
unStringPatForOnDemandJavaScript pat = unpat pat where
  unpat SAny = ""
  unpat (SConst s) = s
  unpat (SCat p1 p2) = unpat p1 ++ unpat p2

-- ---------------------------------------------------------------------------------------------------------------------
  
-- | Sets of properties should be tested for equality solely by the name of the
-- property, not the label on the set.  To this end, all 'ValueSet's are equal. 
data ValueSet c = ValueSet (Label,c)

instance Eq (ValueSet c) where
 _ == _ = True
 
instance Ord (ValueSet c) where
  compare _ _ = EQ

instance Show c => Show (ValueSet c) where
  show (ValueSet s) = show s
  
  
closureThis (AFunction{aFunctionThis=lbl}) = Just lbl
closureThis (ABuiltin{aBuiltinThis=lbl}) = Just lbl
closureThis _ = Nothing

-- |Returns the label of 'AFunction' and 'ABuiltin' values.
functionLabel (AFunction{aFunctionLabel=lbl}) = Just lbl
functionLabel (ABuiltin{aBuiltinLabel=lbl})   = Just lbl
functionLabel _                               = Nothing

isBuiltin (ABuiltin{}) = True
isBuiltin _            = False

hasProperties val = case objectProperties val of
  Just _ -> True
  Nothing -> False

objectProperties (AFunction{aFunctionProps=set}) = Just set
objectProperties (AObject{aObjectProps=set})     = Just set
objectProperties (ABuiltin{aBuiltinProps=(Just lbl)}) = Just (lbl,topContour)
objectProperties (AServerVal{aServerValProps=set}) = Just set
objectProperties _                               = Nothing

isServerVal (AServerVal{}) = True
isServerVal _ = False

isAbstractArray :: Value-> Bool
isAbstractArray (AObject{aObjectX=PArray}) = True
isAbstractArray _ = False

-- |Based on http://developer.mozilla.org/en/docs/Core_JavaScript_1.5_Guide:Conditional_Statements
-- True for undefined, null, 0, NaN, or the empty string ("").
-- If 'isFalseValue v == False', 'v' isn't necessarily a true-value.  It may be indeterminate.
isFalseValue :: Value -> Bool
isFalseValue  UndefinedVal = True
isFalseValue NullVal = True
isFalseValue (ABool False) = True
isFalseValue (ANum n) | n == 0 || isNaN n = True
isFalseValue (AObject{aObjectX=(PString (SConst ""))}) = True
isFalseValue _ = False

isTrueValue :: Value -> Bool
isTrueValue AnyRegexp = True
isTrueValue (ANum n) | n /= 0 && not (isNaN n) = True
isTrueValue (ABool True) = True
isTrueValue (ARegexp{}) = True
isTrueValue (AFunction{}) = True
isTrueValue (ABuiltin{}) = True
isTrueValue (AObject{aObjectX=(PString (SConst ""))}) = False
isTrueValue (AObject{}) = True
isTrueValue _ = False

isUndefinedValue UndefinedVal = True
isUndefinedValue _ = False

isFunction AFunction{} = True
isFunction _ = False

justProperty val@(AProperty{}) = Just val
justProperty _ = Nothing

asPropId AObject{aObjectX=(PString sp)} = case unStringPat sp of
  Just p -> Just p
  Nothing -> Nothing
asPropId (ANum n) = Just $ show (truncate n)
asPropId _ = Nothing

instance AbstractValue Value where
  -- The system wants to add 'newVal' via a cyclic flow.  For now, just add it.  The system will immediately break the
  -- cycle.
  haltCycle newVals existingVals = do
    return newVals


