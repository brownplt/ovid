module Ovid.Prelude 
  ( JsCFAState (..)
  , CFAOpts (..)
  , emptyCFAOpts
  , message
  , warnAt
  , enableUnlimitedRecursion, enablePreciseArithmetic, enablePreciseConditionals
  -- source positions
  , SourcePos, sourceName
  -- Monads
  , module Control.Monad
  , module Control.Monad.Trans
  , module Control.Monad.Identity
  , lift2, lift3
  -- module Control.Monad.State.Strict
  , MonadState (..), StateT, runStateT, evalStateT
  -- lists, numbers, etc
  ,tryInt, L.intersperse, L.isInfixOf, L.isPrefixOf, L.partition
  -- others
  , isJust, fromJust
  , module Scheme.Write
  -- Data.Traversable
  , forM -- Traversable.mapM with arguments flipped; avoid conflicts with Prelude.mapM
  , module Framework
  -- exceptions
  , try, catch, IOException
  ) where

import Prelude hiding (catch)
import Scheme.Write
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceName)
import Control.Monad hiding (mapM,forM)
import Control.Monad.Trans
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State.Strict (StateT,runStateT,evalStateT,get,put,MonadState)
import qualified System.IO as IO
import Data.Maybe
import qualified Data.List as L
import Numeric
import Framework
import Data.Traversable (forM)
import Control.Exception
import CFA.Labels (Label)
import qualified Data.Map as M

message :: MonadIO m => String -> m ()
message s = liftIO (IO.hPutStrLn IO.stdout s)

warnAt str loc = do
  let sLen = length str
  let truncLoc = take (80 - sLen - 7) loc
  warn $ str  ++ " (at " ++ truncLoc ++ ")" 

lift2 m = lift (lift m)
lift3 m = lift (lift2 m)
  
tryInt :: String -> Maybe Int
tryInt s = case readDec s of
  [(n,"")] -> Just n
  otherwise -> Nothing

-- ---------------------------------------------------------------------------------------------------------------------  
  
data JsCFAState ct = JsCFAState { 
  xhrSend :: Maybe Label,
  jscfasBuiltins :: M.Map String Label,
  -- ^function sets passed to 'application'.  Verify that they have at least one function and hopefully no more than
  -- one function.
  jscfaFns :: [(Label,ct)],
  jscfaBranches :: [(Label,ct)],
  jscfaOpts :: CFAOpts,
  jscfaGlobals :: [Label] -- ^list of globals; this is augmented as JavaScript is dynamically loaded
}

--------------------------------------------------------------------------------
-- Options that affect the analysis

-- |Options that control the analysis
data CFAOpts = CFAOpts {
  -- |A recursive function take time exponential (in the number of syntactic
  -- recursive calls) to analyze.  This behavior is also observable for
  -- mutually recursive functions.  By default, the analysis detects this
  -- behavior and halts early.  However, this can break certain libraries
  -- such as Flapjax.
  cfaOptUnlimitedRecursion :: [String],
  -- |By default, we do not perform primitive arithmetic operations.  Instead,
  -- their results are approximated by 'AnyNum'.  However, this approximation
  -- can break common implementations of library functions, such as the
  -- functions in the Flapjax library.
  cfaOptsPreciseArithmetic :: [String],
  -- |The analysis disregards the test expression in conditionals by default.
  cfaOptsPreciseConditionals :: [String]
} deriving (Show)

-- |No options specified.  These are effectively "defaults."  By default,
-- "flapjax/flapjax.js" and "../flapjax/flapjax.js" are permitted to
-- recurse exponentially.  However, in practice, this does not happen, but
-- just allows combinators from flapjax.js to weave through application-specific
-- code.
emptyCFAOpts :: CFAOpts
emptyCFAOpts = 
  CFAOpts ["flapjax/flapjax.js","../flapjax/flapjax.js","DOM.js"]
          ["flapjax/flapjax.js","../flapjax/flapjax.js","DOM.js"]
          ["flapjax/flapjax.js","../flapjax/flapjax.js","DOM.js"]

updateCFAOpts :: (CFAOpts -> CFAOpts) -> JsCFAState ct -> JsCFAState ct
updateCFAOpts f st@JsCFAState{jscfaOpts=opts} = st{jscfaOpts=f opts}

enableUnlimitedRecursion path =
  updateCFAOpts $ \opts -> opts { cfaOptUnlimitedRecursion = path:(cfaOptUnlimitedRecursion opts) }

enablePreciseArithmetic path =
  updateCFAOpts $ \opts -> opts { cfaOptsPreciseArithmetic = path:(cfaOptsPreciseArithmetic opts) }

enablePreciseConditionals path =
  updateCFAOpts $ \opts -> opts { cfaOptsPreciseConditionals = path:(cfaOptsPreciseConditionals opts) }


