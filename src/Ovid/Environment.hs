module Ovid.Environment
  ( Env
  , Ann
  , AdditionalAnnotation (..)
  , AnnotatedExpression
  , AnnotatedStatement
  , extendedStaticEnvironment
  ) where

import WebBits.JavaScript.JavaScript
import WebBits.JavaScript.Environment hiding (Ann,Env)
import CFA.Labels
import Data.Map (Map)
import Data.Generics
import qualified Data.Map as M
--}}}

--{{{ Environment building types and functions 

type AnnotatedExpression = Expression Ann
type AnnotatedStatement = Statement Ann

type Ann = (SourcePos,Label,AdditionalAnnotation)

type Env = Map String Label

data AdditionalAnnotation
  = FnA {
      fnannEnclosing :: Env,
      fnannLocals    :: [Label],
      fnannThisLbl   :: Label 
    }
  | NA
  deriving (Data,Typeable)

instance Show AdditionalAnnotation where
  show _ = "#ann"

incrementLabels incr (stmts,env,lastIndex) = (stmts',env',lastIndex+incr) where
  incrEnv env = M.map (+incr) env
  incrAnnotation (env,idx,loc) = (incrEnv env,idx+incr,loc)
  env' = incrEnv env
  stmts' = map (fmap incrAnnotation) stmts

encapsulateLabels (stmts,env,lastIndex) = (stmts',env',IxLabel lastIndex) where
  encapsulateEnv env = M.map IxLabel env
  encapsulateAnnotation (env,idx,loc) = (encapsulateEnv env,IxLabel idx,loc)
  env' = encapsulateEnv env
  stmts' = map (fmap encapsulateAnnotation) stmts

canonizeLabels (stmts,env,lastIndex) = (stmts',env,lastIndex) where
  stmts' = map (fmap canonizeLabel) stmts
  -- TODO: This is WRONG the FnA is wrong.
  canonizeLabel (env,lbl,pos) = (pos,lbl,FnA env [] lbl) 

dropFreeIds (stmts,freeEnv,globals,nextIndex) = (stmts,globals,nextIndex)

extendedStaticEnvironment :: Int -- ^label of starting node
                          -> [Statement SourcePos]
                          -> ([Statement Ann],Env,Label)
extendedStaticEnvironment startIndex stmts =
  canonizeLabels $ encapsulateLabels $ incrementLabels startIndex $
    dropFreeIds $ staticEnvironment stmts
  
