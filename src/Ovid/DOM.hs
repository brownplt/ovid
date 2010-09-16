-- |Adds constraints for the browser DOM to the environment.
module Ovid.DOM
  ( topLevelIds
  , topLevelPreprocessing
  ) where

--{{{ Imports
import CFA
import CFA.Labels
import Prelude hiding (lookup)
import Ovid.Prelude
import Text.ParserCombinators.Parsec.Pos (initialPos)
import qualified Data.Map as M
import WebBits.JavaScript.JavaScript hiding (Statement)
import qualified WebBits.JavaScript.JavaScript as Js
import Ovid.Abstraction
import Ovid.Environment
import Ovid.ConstraintUtils
--}}}

--{{{ Helpers
type Statement = Js.Statement Ann

noPos = initialPos "Ovid/DOM.hs"

object :: (MonadIO m)
       => Label -- ^ primes this label with 2,3,4
       -> String
       -> Label
       -> [(String,(Label,Contour))]
       -> CfaT Value m Label
object objectLabel name this properties = do
  -- resultant object is stored in objectSet
  ct <- emptyContour
  let objectSet = (objectLabel,ct)
  -- The object has a collection of properties, stored at propSet
  let propLbl = primeLabel objectLabel 1
  let propSet = (propLbl,ct)
  let fnVal = ABuiltin name objectLabel this (Just propLbl)
  -- object has a .prototype property, its value is stored at prototypeSet
  let prototypeLbl = primeLabel propLbl 1
  let prototypeSet = (prototypeLbl,ct)
  newValue (AProperty "prototype" (ValueSet prototypeSet)) propSet
  -- the .prototype property is set to an object, whose properties are stored at baseSet.
  let baseLbl = primeLabel objectLabel 2
  let baseSet = (baseLbl,ct)
  newValue (AObject baseLbl baseSet PNotSpecial) prototypeSet -- the prototypical object (which has no prototype)
  let insertProperty (id,val) = newValue (AProperty id (ValueSet val)) baseSet
  mapM_ insertProperty properties
  newValue fnVal objectSet
  return baseLbl

property id set this = do
  newValue (AProperty id (ValueSet set)) (this,topContour)
  
function name this = do
  lbl <- builtinLabel name
  ct <- emptyContour
  let fn = (ABuiltin name lbl this Nothing)
  newValue fn (lbl,ct)
  return (lbl,ct)

-- |Primes 'lbl' with 2
topFunction name lbl = do
  let this = primeLabel lbl 1
  let ct = topContour
  let fn = ABuiltin name lbl this Nothing
  newValue fn (lbl,ct)
  return (name,lbl)

--}}}

-- |List of names to add to the top-level.
topLevelIds = 
  ["Array","Function","eval","window","XMLHttpRequest","print","String", "addEventListener","document","Element",
   "Object","undefined","$A","$w"]

initArrays lblArray = do
  let this  = primeLabel lblArray 1
  push <- function "Array.push" this
  concat <- function "Array.concat" this
  slice <- function "Array.slice" this
  prototypeLbl <- object lblArray "Array" this [("push",push),("concat",concat),("slice",slice)]
  return [("Array",lblArray),("Array-props",prototypeLbl)]
  
initStrings lblString = do
  let this = primeLabel lblString 1
  any <- function "String.any" this
  prototypeLbl <- object lblString "String" this [("any",any)]
  return [("String",lblString),("String-props",prototypeLbl)]
  
initFunctions lblFunction = do
  let this = primeLabel lblFunction 1
  apply <- function "Function.apply" this
  prototypeLbl <- object lblFunction "Function" this [("apply",apply)]
  return [("Function",lblFunction),("Function-props",prototypeLbl)]
  
initObjects objectLbl = do
  let this = primeLabel objectLbl 1
  prototypeLbl <- object objectLbl "Object" this []
  return [("Object",objectLbl),("Object-props",prototypeLbl)]

initEval evalLbl = do
  let this = primeLabel evalLbl 1
  eval <- function "eval" this
  evalSet <- emptyContour >>= \ct -> return (evalLbl,ct)
  subsetOf eval evalSet
  return [("eval",evalLbl)]
  
initWindow windowLbl = do
  let this = primeLabel windowLbl 1
  addEventListener <- function "window.addEventListener" this
  prototypeLbl <- object windowLbl "window" this
    [("addEventListener",addEventListener)]
  return [("window",windowLbl),("window-props",prototypeLbl)]

initElements eltLbl = do
  let this = primeLabel eltLbl 1
  prototypeLbl <- object eltLbl "Element" this []
  return [("Element",eltLbl),("Element-props",prototypeLbl)]
  
initDocument documentLbl = do
  let this = primeLabel documentLbl 1
  -- getElementByTagName <- function "document.getElementByTagName" this
  -- getElementById <- function "document.getElementById" this
  write <- function "document.write" this
  property "write" write this 
  newValue (AObject documentLbl (this,topContour) PNotSpecial {- but it is!!! -}) (documentLbl,topContour)
  return [("document",documentLbl)]
  
  
initXMLHttpRequest xhrLbl = do
  let this = primeLabel xhrLbl 1
  send <- function "XMLHttpRequest.send" this
  open <- function "XMLHttpRequest.open" this
  prototypeLbl <- object xhrLbl "XMLHttpRequest" this [("send",send),("open",open)]
  return [("XMLHttpRequest-props",prototypeLbl),("XMLHttpRequest",xhrLbl), ("XMLHttpRequest:send",fst send)]

  
lookup k m = case M.lookup k m of
  Nothing -> fail $ "lookup: key not found--" ++ show k
  Just v -> return v
  
-- |Preprocessing before interpreting any files
topLevelPreprocessing :: (MonadIO m)
                      => M.Map String Label -- ^top level names
                      -> CfaT Value
                              (StateT (JsCFAState Contour) m)
                              (M.Map String Label)
topLevelPreprocessing topLevel = do
  let def fn = lookup fn topLevel >>= topFunction fn
  arrayNames <- lookup "Array" topLevel >>= initArrays
  strings <- lookup "String" topLevel >>= initStrings
  elements <- lookup "Element" topLevel >>= initElements
  objects <- lookup "Object" topLevel >>= initObjects
  functionNames <- lookup "Function" topLevel >>= initFunctions
  evalNames <- lookup "eval" topLevel >>= initEval
  print <- def "print"
  dollarA <- def "$A"
  dollarw <- def "$w"
  addEventListener <- def "addEventListener"
  windowNames <- lookup "window" topLevel >>= initWindow
  documentNames <- lookup "document" topLevel >>= initDocument
  xhrNames <- lookup "XMLHttpRequest" topLevel >>= initXMLHttpRequest
  -- bind undefined
  newValue UndefinedVal (runIdentity $ lookup "undefined" topLevel,topContour)
  return $ M.union topLevel $ M.fromList $ dollarA : dollarw : print : addEventListener: (evalNames ++ arrayNames 
    ++ functionNames ++ windowNames ++ xhrNames ++ documentNames ++ strings ++ elements ++ objects)
