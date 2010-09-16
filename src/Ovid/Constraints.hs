-- |Constraints that specify a control flow analysis for Javascript. 
module Ovid.Constraints 
  ( initialize
  , stmt
  , expr
  , AnnotatedStatement
  , AnnotatedExpression
  , ParentNodeT
  , JsCFAState(..)
  , CFAOpts (..)
  ) where

-- #define CONSERVATIVE_MODE
-- #define DEBUG_XHR
-- #define DEBUG_BUILTINS
-- #define CONSERVATIVE_REFERENCES
-- #define CONSERVATIVE_LVALS
-- #define TRACE_APPLICATION
-- #define TRACE_ASSIGNMENT
-- #define PENTIUM_MMX_LOOP_OPTIMIZATIONS
  
import Prelude hiding (catch)
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Foldable as F
import Data.Generics
import Data.Typeable
import Framework
import WebBits.JavaScript.JavaScript hiding (Expression,Statement)
import qualified WebBits.JavaScript.JavaScript as Js
-- 'buildJsEnv' is required for `on-demand JavaScript'
import Ovid.Environment (Ann,AdditionalAnnotation(..),AnnotatedExpression, 
  AnnotatedStatement)
import CFA.Labels
import Ovid.Abstraction
import CFA
import Ovid.Prelude
import Data.InductiveGraph.Class
import Ovid.ConstraintUtils
import Ovid.Interactions
-- required for `on demand JavaScript'
import WebBits.Html.Html (parseHtmlFromString,parseHtmlFromFile)
import WebBits.JavaScript.Crawl (getPageJavaScript)
import Ovid.DOM (topLevelIds)
import qualified System.IO as IO
import Data.Store
-- -----------------------------------------------------------------------------
-- Miscellaneous

primNumeric OpAdd = Just (+)
primNumeric OpMul = Just (*)
primNumeric OpDiv = Just (/)
primNumeric OpSub = Just (-)
primNumeric _     = Nothing

primLogical OpLT = Just (<)
primLogical OpLEq = Just (<=)
primLogical OpGT = Just (>)
primLogical OpGEq = Just (>=)
primLogical _ = Nothing

logicalAssignOps
  = [OpAssignBAnd, OpAssignBXor, OpAssignBOr]
  
numericAssignOps
  = [OpAssignAdd, OpAssignSub, OpAssignMul, OpAssignDiv, OpAssignMod,
     OpAssignLShift, OpAssignSpRShift, OpAssignZfRShift]
     
logicalInfixOps = [OpLT .. OpLOr]

arithmeticInfixOps = [OpMul .. OpBOr]

lookupErr :: (Monad m, Ord k) => String -> k -> M.Map k v -> m v
lookupErr errStr k t =
  case M.lookup k t of
    Just k  -> return k
    Nothing -> fail ("Ovid.Constraints: " ++ errStr)

idv :: Monad m => Id Ann -> m Label
idv (Id (_,lbl,_) _) = return lbl

type Expression = Js.Expression Ann
type Statement = Js.Statement Ann

type ParentNodeT n m = StateT n m

-- |We need to be able to have multiple invocations of document.write on the stack.
isRecursionAllowed _ lbl | isBuiltinLabel lbl = True
isRecursionAllowed srcs lbl = case labelSource lbl of
  Nothing -> False
  Just src -> src `elem` srcs

isPreciseArithmetic lbl = do
  JsCFAState { jscfaOpts = opts } <- lift get
  case labelSource lbl of
    Nothing -> return False
    Just src -> return (src `elem` cfaOptsPreciseArithmetic opts)

isPreciseConditionals lbl = do
  JsCFAState { jscfaOpts = opts } <- lift get
  case labelSource lbl of
    Nothing -> return False
    Just src -> return (src `elem` cfaOptsPreciseConditionals opts)

    
application :: (MonadIO m) 
            => (Label,Contour)   -- ^set of functions
            -> [(Label,Contour)] -- ^sets of arguments
            -> Contour           -- ^dynamic call stack
            -> (Label,Contour)   -- ^result set (out-flow)
            -> CfaT Value (StateT (JsCFAState Contour) m) ()
application svF actuals ct svCxt = do
  -- Mark 'svF' as a function set.  After the analysis is complete, we can check if any function values flowed into this
  -- set.  If not, it's a good sign that we missed modelling some part of the DOM.
  markFunctionSet svF
  -- Options governing the analysis.
  JsCFAState { jscfaOpts = opts } <- lift get
  let expSrcs = cfaOptUnlimitedRecursion opts
  -- Invoke callback for a piggybacked analysis.
  -- applicationHook <- callHook svF actuals ct svCxt
  let app fn@(ABuiltin{aBuiltinName=name,aBuiltinLabel=lbl, aBuiltinThis=this}) = do
{- #ifdef TRACE_APPLICATION
        warn $ "builtin application; lbl " ++ show lbl
#endif -}
        -- warn $ "Applying " ++ show lbl
        builtinDispatch name ct ((this,ct):actuals) svCxt
        -- dummy 'return []' or we violate let-polymorphism!
        -- applicationHook fn (dispatch >> return []) 
        return ()
      -- Check to see if this function is on the stack.  If it is, we don't
      -- apply it, unless its label indicates that it should be permitted to
      -- recurse.
      app fn@(AFunction{aFunctionLabel=lbl}) 
        | lbl `elem` callStack ct && (not $ isRecursionAllowed expSrcs lbl) = do
        warn $ "Ignoring an application of " ++ show lbl ++ " from " ++ show (fst svCxt) 
        return ()
      app fn@(AFunction{aFunctionLabel=lbl,aFunctionArgs=formals,aFunctionLocals=locals,aFunctionBody=(EqualOrd body),
                        aFunctionEnv=ceClosure,aFunctionThis=thisLbl}) = do
{- #ifdef  TRACE_APPLICATION
        warn $ "Call stack of length " ++ (show $ length $ callStack ct)
#endif -}
        size <- currentSetSize svF
        -- warn $ "Applying " ++ show lbl
        when (size > 5) 
          (warn $ "WARNING: " ++ show size ++ " functions in a function set")
        let svFormals = map (\lbl -> (lbl,ct)) formals
        let svLocals  = map (\lbl -> (lbl,ct)) locals
        let this = (thisLbl,ct)
        let ce = M.union (M.fromList (svFormals ++ svLocals)) ceClosure
        -- create the array of arguments
        argumentsLbl <- uniqueLabel
        let arguments = (argumentsLbl,ct)
        newArray arguments actuals
        -- flow actuals into the formals in this contour
        mapM_ (uncurry subsetOf) (zip (this:arguments:actuals) svFormals)
        -- flow undefined into the arguments that are not supplied
        let undefinedArgs = drop (length $ this:arguments:actuals) svFormals
        mapM_ (newValue UndefinedVal) undefinedArgs 
        -- flow the results into the context of the call
        svResults <- {- applicationHook fn -} (stmt ce (newCall lbl ct) body)
        mapM_ (\set -> subsetOf set svCxt) svResults
      app UndefinedVal = return ()
      app v = do
        warn $ "Ovid.Constraints.application: non-function in " ++ 
               "function set : " ++ show v
        warn $ "function at " ++ show svF
  propagateTo svF svCxt app

showProp (PropId _ id) = show id
showProp (PropString _ s) = s
showProp (PropNum _ n) = show n


-- |Generates constraints for the expression.
expr :: (MonadIO m)
     => M.Map Label Contour
     -> Contour
     -> AnnotatedExpression
     -> CfaT Value (StateT (JsCFAState Contour) m) (Label,Contour)
expr ce ct e = {- exprHook ce ct e >>= \r -> -} case e of	     
  StringLit (_,lbl,_) s -> do
    -- This represents a standard problem. The object we create must have the label lbl' since its the only concrete
    -- label available in this expression.  Suppose the outer expression is an application.  In an application, we must
    -- prime the values sets of the argument array.  We cannot prime the formal-labels, as they are shared between
    -- applications.  So, we have to prime the arguments.  However, since this is an argument, it is already primed.
    newString (lbl,ct) (SConst s)
    return (lbl,ct)
  RegexpLit (_,lbl,_) s b c -> do
    newValue (ARegexp s b c) (lbl,ct)
    return (lbl,ct)
  NumLit (_,lbl,_) n -> do 
    newValue (ANum n) (lbl,ct)
    return ( lbl,ct)
  BoolLit (_,lbl,_) b -> do
    newValue (ABool b) (lbl,ct)
    return ( lbl,ct)
  NullLit (_,lbl,_) -> do 
    newValue (NullVal) (lbl,ct)
    return ( lbl,ct)
  ArrayLit (_,lbl,_) es -> do
    elems <- mapM (expr ce ct) es
    newArray (lbl,ct) elems
    return (lbl,ct)
  ObjectLit (_,lbl,_) props -> do
    let prop (p,e) = do
          eSet <- expr ce ct e
          return (showProp p,eSet)
    propSets <- mapM prop props
    newObject (lbl,ct) propSets
    return (lbl,ct)
  ThisRef (_,lbl,_) -> do
    thisCt <- lookupErr ("`this' is unbound") lbl ce
    return (lbl,thisCt)
  VarRef (_,lbl,_) id -> do -- a bound identifier; not an assignment
    idCt <- lookupErr ("unbound identifier: " ++ show id) lbl ce
    subsetOf (lbl,idCt) (lbl,ct)
    return (lbl,ct) -- we *always* return the context
  DotRef (_,lbl,_) obj (Id _ propId) -> do -- obj.prop
    objSet <- expr ce ct obj
    propagateProperty objSet (lbl,ct) propId $ \propSet -> subsetOf propSet (lbl,ct)
    return (lbl,ct)
  BracketRef (_,lbl,_) obj prop -> do -- obj[prop]
    let stx = (lbl,ct)
    objStx <- expr ce ct obj
    propIdStx <- expr ce ct prop
    flow1 objStx stx (const Nothing)    
    propagateTo propIdStx stx $ \propVal -> case propVal of
      AObject{aObjectX=(PString sp)} -> case unStringPat sp of
        Just propId -> do

          unsafePropagateProperty objStx stx propId $ \vals -> subsetOf vals stx
        Nothing -> do
          warnAt "indeterminate string used for property reference" (show ct)
          propagatePropertySetTo objStx stx $ \set -> propagate set $ \val -> case val of
            AProperty _ (ValueSet valSet) -> subsetOf valSet stx
            otherwise -> fail $ "non-property value in property set at " ++ show stx ++ "; value is " ++ show val
      ANum propIx -> 
        unsafePropagateProperty objStx stx (show $ truncate propIx) $ \vals -> subsetOf vals stx
      AnyNum -> do 
        -- This is far too common with arrays.
        -- warnAt "indeterminate number used for property reference" (show ct)
        propagatePropertySetTo objStx stx $ \set -> propagate set $ \val -> case val of
          AProperty _ (ValueSet valSet) -> subsetOf valSet stx
          otherwise -> fail $ "non-property value in property set at " ++ show stx ++ "; value is " ++ show val
      UndefinedVal -> return ()
      otherwise -> 
        warn $  "non-indexable value (" ++ show propVal ++ ") at " ++ show stx
    return stx
  NewExpr (_,lbl,_) constr args -> do
    -- We are essentially setting up a function call; the only difference is the construction of `this.'
    constrSet <- expr ce ct constr -- the function / constructor
    argSets <- mapM (expr ce ct) args
    -- the contour of the function call
    ct' <- extendContour lbl ct
    -- discard the return value of the function; note that the result flows
    -- into (lbl,ct') so that we can tell when we are applying at the edge of
    -- the contour.  However, the result set is (lbl,ct).
    application constrSet argSets ct' (lbl,ct')
    propagateTo constrSet (lbl,ct) $ \val -> case (closureThis val,objectProperties val) of
      (Just this,Nothing) -> do -- builtin with no prototype
        subsetOf (this,ct') (lbl,ct)
      (Just this,Just propSet) -> do -- function/builtin with a prototype
        -- create an empty object
        obj@(AObject{aObjectProps=props}) <- newObject (this,ct') []
        -- copy the members of the prototype over
        propagatePropertyOf val (lbl,ct) "prototype" $ \proto -> propagatePropertySetTo proto props $ \propSet -> do
          flow1 propSet props justProperty
        -- obj.prototype = constr
        newValue (AProperty "prototype" (ValueSet constrSet)) props
        -- flow the set of objects (thises) into the result
        subsetOf (this,ct') (lbl,ct)
      otherwise -> do
        warn $ "non-function value " ++ show val ++ " in " ++ show e
    return (lbl,ct)
  PostfixExpr (_,lbl,_) op e -> do -- e++ or e--
    eSet <- expr ce ct e
    flow1 eSet eSet $ \val -> case val of
      ANum _ -> Just AnyNum
      otherwise -> Nothing
    subsetOf eSet (lbl,ct)
    return (lbl,ct)
  PrefixExpr (_,lbl,_) op e -> do
    eSet <- expr ce ct e
    stringPrototype <- builtinPrototype "String"
    flow1 eSet eSet $ \val -> case val of
      ANum _ -> Just AnyNum
      ABool _ -> Just AnyBool
      otherwise -> Nothing
    flow1 eSet (lbl,ct) $ \val -> case op of
      -- ++e and --e are the only operators that side-effect e
      PrefixInc -> Just AnyNum
      PrefixDec -> Just AnyNum
      PrefixLNot -> case val of
        _ | isTrueValue val -> Just (ABool False)
        _ | isFalseValue val -> Just (ABool True)
        otherwise -> Just AnyBool
      PrefixBNot -> Just AnyNum
      PrefixPlus -> Nothing -- e == +e
      PrefixMinus -> Just AnyNum
      PrefixTypeof -> case val of
        AFunction{} -> Just $ AObject (primeLabel lbl 1) stringPrototype (PString $ SConst "function")
        otherwise -> Just AnyBool
      -- TODO : distinction between void and undefined? check!
      PrefixVoid -> Just UndefinedVal 
      PrefixDelete -> Just UndefinedVal 
    return (lbl,ct)
  InfixExpr (_,lbl,_) op l r -> do
    let cxt = (lbl,ct)
    lVar <- expr ce ct l
    rVar <- expr ce ct r
    isPrecise <- isPreciseArithmetic lbl -- do you expect us to actually add?
    isPreciseIf <- isPreciseConditionals lbl -- do you expect us to actually branch?
    let prototype = primeSet cxt 1 -- we may use this
    case op of
      OpLOr -> flow2 lVar rVar cxt $ \lv rv -> 
               if isTrueValue lv then
                 Just lv
               else if isFalseValue lv then
                 Just rv
               else
                 Just AnyBool
      _ | op `elem` [OpLT,OpLEq,OpGT,OpGEq,OpIn,OpEq,OpNEq,OpStrictEq,OpStrictNEq,OpLAnd,OpIn] ->
          flow2 lVar rVar cxt $ \l r -> case (l,r,primLogical op) of
            (ANum m,ANum n,Just op) -> Just $ if m `op` n then (ABool True) else (ABool False)
            (AObject{aObjectX=(PString sp1)},AObject{aObjectX=(PString sp2)},Nothing) | op == OpLEq ->
              Just $ ABool (sp1 == sp2)
            otherwise -> Just AnyBool
      _ | op `elem` [OpMul,OpDiv,OpMod,OpSub] -> flow2 lVar rVar cxt $ \l r -> case (l,r,primNumeric op) of
        (ANum m,ANum n,Just op) -> Just $ ANum (m `op` n)
        otherwise -> Just AnyNum
      _ | op `elem` [OpLShift,OpSpRShift,OpZfRShift,OpBAnd,OpBXor,OpBOr] ->
          flow2 lVar rVar cxt $ \_ _ -> Just AnyNum
      OpInstanceof -> flow2 lVar rVar cxt $ \val prototype -> case (val,prototype) of
        (AObject{aObjectX=PString{}}, ABuiltin{aBuiltinName="String"}) -> Just (ABool True)
        (_                          , ABuiltin{aBuiltinName="String"}) -> Just (ABool False)
        (AObject{aObjectX=PArray},ABuiltin{aBuiltinName="Array"}) -> Just (ABool True)
        (AObject{aObjectX=PArray},_) -> Just (ABool False)
        otherwise -> Just AnyBool
      OpAdd -> flow2 lVar rVar cxt $ \l r -> case (l,r) of
        (ANum m,ANum n) | isPrecise -> Just $ ANum (m+n)
                        | otherwise -> Just AnyNum
        (ANum _,AnyNum) -> Just AnyNum
        (AnyNum,_) -> Just AnyNum
        (AObject{aObjectX=(PString s)},AObject{aObjectX=(PString t)}) ->
          Just $ (AObject lbl prototype (PString $ stringPatCat s t)) 
        (AObject{aObjectX=(PString s)}, ANum n) ->
          Just $ (AObject lbl prototype (PString $ stringPatCat s (SConst $ show n)))
        (AObject{aObjectX=(PString s)},_) ->
          Just $ (AObject lbl prototype (PString $ stringPatCat s SAny))
        otherwise -> Nothing
      otherwise -> fail $ "Ovid.Constraints.expr : unaccounted infix operator -- " ++ show op
    -- flow primitive prototypes as needed
    stringPrototype <- builtinPrototype "String"
    propagate cxt $ \val -> case val of
      AObject{aObjectX=(PString _),aObjectProps=props} -> subsetOf stringPrototype props
      otherwise -> return ()
    return cxt
  CondExpr (_,lbl,_) test true false -> do
    expr ce ct test 
    trueVar <- {- branchHook r -} (expr ce ct true)
    falseVar <- {- branchHook r -} (expr ce ct false)
    subsetOf trueVar (lbl,ct)
    subsetOf falseVar (lbl,ct)
    -- joinHook [trueR,falseR] r
    return (lbl,ct)
  AssignExpr (_,lbl,_) op l r
    | op == OpAssign -> do
        lVar <- lval ce ct l
        rVar <- expr ce ct r
        subsetOf rVar lVar
        subsetOf lVar (lbl,ct)
        return (lbl,ct)
    | op `elem` logicalAssignOps -> do
        lVar <- lval ce ct l
        rVar <- expr ce ct r
        flow1 rVar lVar $ \_ -> Just AnyBool
        subsetOf lVar (lbl,ct)
        return (lbl,ct)
    | op `elem` numericAssignOps -> do
        lVar <- lval ce ct l
        rVar <- expr ce ct r
        flow1 rVar lVar $ \_ -> Just AnyNum
        subsetOf lVar (lbl,ct)
        return (lbl,ct)
    | otherwise -> do
        fail $ "Program bug: the operator " ++ show op ++ " was unclassified"
  ParenExpr _ e -> 
    expr ce ct e
  ListExpr _ [] -> 
    fail "Ovid.Constraints.expr : empty list expression (program bug)"
  ListExpr (_,lbl,_) es -> do
    eVars <- mapM (expr ce ct ) es
    subsetOf (last eVars) (lbl,ct)
    return (lbl,ct)
  CallExpr (_,lbl,_) f@(DotRef (_,methodLbl,_) obj (Id _ propId)) args -> do
    let cxt = (lbl,ct)
    objSet <- expr ce ct obj -- the object whose method we are caling
    argSets <- mapM (expr ce ct) args -- the arguments to the method
    ct' <- extendContour lbl ct -- contour of the call
    application (methodLbl,ct) argSets ct' (lbl,ct) -- flow the method into (methodLbl,ct), for consistency
    propagateProperty objSet cxt propId $ \fnSet -> do
      subsetOf fnSet (methodLbl,ct)
      propagateTo fnSet cxt $ \fnVal -> case closureThis fnVal of -- setup `this'
        Just thisLbl -> subsetOf objSet (thisLbl,ct')
        Nothing -> return () -- `application' will handle the warning
    return (lbl,ct)
  CallExpr (_,lbl,_) f@(BracketRef (_,methodLbl,_) obj prop) args -> do
    let cxt = (lbl,ct)
    objSet <- expr ce ct obj
    propSet <- expr ce ct prop
    argSets <- mapM (expr ce ct) args
    ct' <- extendContour lbl ct -- contour of the call
    application (methodLbl,ct) argSets ct' (lbl,ct) -- the application *must* be here for the call graph
    propagateTo propSet cxt $ \propVal -> case asPropId propVal of -- select the value of the property
      Nothing -> warn $ "indeterminate index at " ++ show propSet ++ "; value is " ++ show propVal
      Just propId -> propagateProperty objSet cxt propId $ \fnSet -> do
        subsetOf fnSet (methodLbl,ct)
        propagateTo fnSet cxt $ \fnVal -> case closureThis fnVal of -- setup `this'
          Just thisLbl -> subsetOf (objSet) (thisLbl,ct')
          Nothing -> return () -- application will display a warning
    return (lbl,ct)          
  CallExpr (_,lbl,ann) f args -> do
{- #ifdef  TRACE_APPLICATION
    warn $ "call: " ++ (show f)
#endif -}
    (f:args) <- mapM (expr ce ct) (f:args)
    ct' <- extendContour lbl ct
    application f args ct' (lbl,ct)
    return (lbl,ct)
  FuncExpr (_,lbl,FnA{fnannEnclosing=enclosing,fnannLocals=locals,fnannThisLbl=thisLbl}) 
           args body  -> do
    formals <- mapM idv args
    -- the function value creates an implicit object
    let objSet = primeSet (lbl,ct) 1
    -- members of Function.prototype are copied to the function object
    -- TODO: object.prototype = Function
    JsCFAState {jscfasBuiltins=builtins} <- lift get
    prototypeSet <- builtinPrototype "Function"
    subsetOf prototypeSet objSet
    newValue (AFunction lbl formals locals (EqualOrd body) ce objSet thisLbl) (lbl,ct) -- acceptable newValue
    return (lbl,ct)
  FuncExpr (_,_,ann) _ _ -> 
    fail $ "(bug) Ovid.Constraints.expr: unexpected annotation on a function"
           ++ show ann ++ ", function was " ++ show e 

      
      
-- The label on e must be returned. (er. why?)
lval :: (MonadIO m)
     => M.Map Label Contour
     -> Contour
     -> AnnotatedExpression
     -> CfaT Value (StateT (JsCFAState Contour) m) (Label,Contour)
lval ce ct expr@(VarRef (_,lbl,_) id) = do
  ct' <- lookupErr ("lval : " ++ show lbl ++ " is not in ce :" ++ show id ++ "\n" ++ show expr) lbl ce
  return (lbl,ct')
lval ce ct (DotRef (_,lbl,_) obj (Id _ propId)) = do -- obj.prop
  objSet <- expr ce ct obj
  propagateProperty objSet (lbl,ct) propId $ \valSet -> do
    {-flow1 (lbl,ct) valSet (const Nothing)
    propagate (lbl,ct) $ \val -> do
      clearValues valSet
      newValue val valSet -}
    removeValue UndefinedVal valSet
    subsetOf (lbl,ct) valSet
  return (lbl,ct)
lval ce ct e@(BracketRef (_,lbl,_) obj prop) = do -- obj[prop]
  let stx = (lbl,ct)
  objSet <- expr ce ct obj
  propSet <- expr ce ct prop
  flow1 objSet (lbl,ct) (const Nothing)
  propagateTo propSet stx $ \propVal -> case asPropId propVal of
    Just propId -> unsafePropagateProperty objSet (lbl,ct) propId $ \valSet -> do
      {-flow1 (lbl,ct) valSet (const Nothing)
      propagate (lbl,ct) $ \val -> do
        clearValues valSet
        newValue val valSet-}
      removeValue UndefinedVal valSet
      subsetOf (lbl,ct) valSet
    Nothing | propVal == UndefinedVal -> return ()
            | otherwise -> do
      warn $ "Indeterminate index at " ++ show stx ++ "--assigning to all values.  The index was " ++ show propVal
      propagatePropertySetTo objSet stx $ \propSet -> propagateTo propSet (lbl,ct) $ \propVal -> case propVal of --TODO : overstructured
        AProperty _ (ValueSet valSet) -> subsetOf (lbl,ct) valSet
        otherwise -> warn $ "non-property at " ++ show (lbl,ct) ++ "; value is " ++ show propVal
  return (lbl,ct)
lval _ _ e = fail $ "Invalid l-value: " ++ show e

caseClause ce ct (CaseClause l e ss) = 
  expr ce ct e >> mapM (stmt ce ct ) ss >>= return . concat
caseClause ce ct (CaseDefault l ss) = 
  mapM (stmt ce ct ) ss >>= return . concat

catchClause ce ct (CatchClause l id s) = stmt ce ct s

varDecl ce ct (VarDecl _ _ Nothing) = return []
varDecl ce ct e'@(VarDecl (_,idLabel,_) _ (Just e)) = do
  case M.lookup idLabel ce of
    Just idCt -> do
      eSet <- expr ce ct e
      subsetOf eSet (idLabel,idCt)
      return []
    Nothing -> fail $ "varDecl: could not find contour for " ++ (show e') ++
                      "\n\n" ++ "the environment is " ++ show ce ++ "\n\n" ++
                      "the label is " ++ show idLabel


forInit ce ct NoInit = return []
forInit ce ct (VarInit decls) = mapM (varDecl ce ct) decls >>= return . concat 
forInit ce ct (ExprInit e) = expr ce ct e >> return []

forInInit (ForInVar id)   = id
forInInit (ForInNoVar id) = id

yl:: (Monad m) => (a -> m [b]) -> Maybe a -> m [b]
yl f Nothing = return []
yl f (Just x) = f x
        

stmt :: (MonadIO m)
     => M.Map Label Contour -- ^environment
     -> Contour             -- ^contour
     -> Statement
     -> CfaT Value (StateT (JsCFAState Contour) m) [(Label,Contour)]
stmt ce ct s = {- stmtHook ce ct s >>= \r -> -} case s of
  BlockStmt l ss -> do
    vss <- mapM (stmt ce ct) ss
    return (concat vss)
  EmptyStmt _ ->
    return []
  ExprStmt l e ->
    expr ce ct e >> return []
  IfStmt (_,lbl,_) e s1 s2 -> do
    let stx = (lbl,ct)
    testStx <- expr ce ct e
    markBranch testStx
    propagateTo testStx stx $ \testVal -> -- constraint identity will evaluate true/false branches at most once
      if isTrueValue testVal then do
        results <- stmt ce ct s1
        mapM_ (\result -> subsetOf result stx) results
      else if isFalseValue testVal then do
        results <- stmt ce ct s2
        mapM_ (\result -> subsetOf result stx) results
      else {- is indeterminate value -} do
        trueResults <- stmt ce ct s1
        falseResults <- stmt ce ct s2
        mapM_ (\result -> subsetOf result stx) (trueResults ++ falseResults)
    return [stx]        
    {-
    isPrecise <- isPreciseConditionals lbl
    {- (s1r,s1vs) <- branchHook r (stmt ce ct s1)
    (s2r,s2vs) <- branchHook r (stmt ce ct s2)
    joinHook [s1r,s2r] r
    return (s1vs ++ s2vs) -}
    if isPrecise
       -- when using precise conditionals, we don't generate the branch in the
       -- control flow graph
      then do
        let result = primeSet (lbl,ct) 1
        propagateTo test (lbl,ct) $ \testVal -> case testVal of
          ABool True -> do
            vs <- stmt ce ct s1
            mapM_ (\set -> subsetOf set result) vs
          ABool False -> do
            vs <- stmt ce ct s2
            mapM_ (\set -> subsetOf set result) vs
          otherwise ->
            warnAt "imprecise boolean value with precise conditionals" (show ct)
        return [result]
      else do
        (s1r,s1vs) <- branchHook r (stmt ce ct s1)
        (s2r,s2vs) <- branchHook r (stmt ce ct s2)
        joinHook [s1r,s2r] r
        return (s1vs ++ s2vs) -}
  IfSingleStmt (_,lbl,_) testExpr bodyStmt -> do
    let stx = (lbl,ct)
    testStx <- expr ce ct testExpr
    markBranch testStx
    propagateTo testStx stx $ \testVal ->
      if not (isFalseValue testVal) then do
        results <- stmt ce ct bodyStmt
        mapM_ (\result -> subsetOf result stx) results
      else return ()
    return [stx]
  SwitchStmt l e cs ->
    expr ce ct e >> mapM (caseClause ce ct ) cs >>= return . concat 
  WhileStmt l e s ->
    expr ce ct e >> stmt ce ct s
  DoWhileStmt l s e ->
    expr ce ct e >> stmt ce ct s
  BreakStmt l yid ->
    return []
  ContinueStmt l yid ->
    return []
  LabelledStmt l id s ->
    stmt ce ct s
  ForInStmt (_,lbl,_) init e body -> do -- we unroll for-in loops
    let stx = (lbl,ct)
    let (Id (_,varLbl,_) varId) = forInInit init
    stringPrototype <- builtinPrototype "String"
    eStx <- expr ce ct e
    propagateTo eStx stx $ \obj -> case objectProperties obj of
      Nothing | obj == NullVal -> return ()
              | otherwise -> return () -- warn $ "for-in : non-object value (" ++ show obj ++ ") at " ++ show eStx
      Just propSet -> propagateTo propSet stx $ \property -> case property of -- propSet is unique for each object
        AProperty propId _ | (not $ isAbstractArray obj) || (isJust $ tryInt propId) -> do
          ct' <- extendContour (propLabel varLbl propId) ct
          newString (varLbl,ct') (SConst propId)
          results <- stmt (M.insert varLbl ct' ce) ct' body
          mapM_ (\result -> subsetOf result stx) results
        -- TODO: not quite right, for-in iterates over non-int indices that are not in the prototype
        AProperty _ _ | isAbstractArray obj -> return ()
        otherwise -> fail $ "non-property value in property set at " ++ show eStx
    return [stx]
  -- special case: for (var id = initExpr; testExpr; id++) bodyStmt (we do postfix decrement here too)
  {-
  ForStmt (_,lbl,_) (VarInit [VarDecl (_,idLbl,_) _ (Just initExpr)]) (Just testExpr) (
          (Just $ PostfixExpr _ postfixOp (VarRef (_,incrIdLbl,_) _)) bodyStmt | idLbl == incrIdLbl -> do
    let stx = (lbl,ct)
    initStx <- expr ce ct initExpr
    let iterate idStx ix  =
          ct' <- extendContour (primeLabel idLbl ix) ct
          -- must extend the contour of the call, or the inner constraints won't get created uniquely for each run
          testStx <- expr (M.insert idLbl ct' ce) ct' testExpr
          propagate testStx $ \testVal -> case testVal of
            _ | isFalseValue testVal -> do
              return ()
            otherwise -> do
              
            
            
    propagateTo initStx stx $ \init -> do
      testStx <- expr (M.insert idLbl ct' ce) ct' testExpr
    -}  
  ForStmt (_,lbl,_) init ye1 ye2 s -> do
    forInit ce ct init
    ym (expr ce ct ) ye1
    ym (expr ce ct ) ye2
    stmt ce ct s
  TryStmt l s cs ys -> do
    sv <- stmt ce ct s
    cvs <- mapM (catchClause ce ct ) cs
    fvs <- yl (stmt ce ct ) ys
    return (sv ++ (concat cvs) ++ fvs)
  ThrowStmt l e ->
    expr ce ct e >> return []
  ReturnStmt l Nothing ->
    return [] -- TODO : perhaps undefined?
  ReturnStmt _ (Just e) ->
    expr ce ct e >>= \v -> return [v]
  WithStmt loc e s ->
    expr ce ct e >> stmt ce ct s
  VarDeclStmt loc ds ->
    mapM_ (varDecl ce ct ) ds >> return []
  FunctionStmt (_,_,FnA{fnannEnclosing=enclosing, fnannLocals=locals, fnannThisLbl=thisLbl}) id args body -> do
    lbl <- idv id -- the only difference from FuncExpr is the label
    formals <- mapM idv args
    -- the function value creates an implicit object
    let objSet = primeSet (lbl,ct) 1
    -- members of Function.prototype are copied to the function object
    -- TODO: object.prototype = Function
    JsCFAState {jscfasBuiltins=builtins} <- lift get
    prototypeSet <- builtinPrototype "Function"
    subsetOf prototypeSet objSet
    newValue (AFunction lbl formals locals (EqualOrd body) ce objSet thisLbl) (lbl,ct) -- acceptable newValue
    return []
  FunctionStmt (_,_,ann) _ _ _  -> 
    fail $ "(bug) Ovid.Constraints.stmt: unexpected annotation on a function"
           ++ show ann ++ ", function was " ++ show s 
         
-- |The <unsafe> is necessary to handle leading holes.
onDemandJavaScript :: (MonadIO m)
                   => Contour -> StringPat -> String 
                   -> CfaT Value (StateT (JsCFAState Contour) m) ()
onDemandJavaScript ct sp sourceName = do
  let concreteHtml = "<unsafe>" ++ unStringPatForOnDemandJavaScript sp ++ "</unsafe>" -- deals with holes!!
  warn $ "HTML: " ++ show concreteHtml
  case parseHtmlFromString sourceName concreteHtml of
    Left err -> do warn $ "onDemandJavaScript: " ++ show err
                   liftIO $ putStrLn $ "onDemandJavaScript: " ++ show err
    Right (htmlStx,_) -> do
      parsedStmts <- liftIO $ getPageJavaScript htmlStx
      dynamicJavaScriptLoader ct parsedStmts

dynamicJavaScriptLoader ct parsedStmts = do
  globals <- getGlobals
  fail "dynamicJavaScriptLoader is temporarily disabled"
  {- (globals,stmts) <- makeDynamicEnv globals parsedStmts
  setGlobals globals
  -- (envTree,stmts) <- buildJsEnv topLevelIds parsedStmts
  warn $ (show $ length stmts) ++ " statements are on-demand"
  let ce = M.fromList $ map (\lbl -> (lbl,topContour)) globals
  -- This is correct.  Execution is _not_ in the top contour.  If it were, our beautiful recursion check
  -- goes out the door.  Moreover, the analysis may not terminate in general, if, for example, factorial
  -- made its recursive call `on-demand' and we let it happen in the top contour.
  mapM (stmt ce ct) stmts
  return () -}

dynamicIFrameLoader :: (MonadIO m)
                   => Contour -> StringPat
                   -> CfaT Value (StateT (JsCFAState Contour) m) ()
dynamicIFrameLoader ct sp = do
  let src = unStringPatForOnDemandJavaScript sp
  result <- liftIO $ try (parseHtmlFromFile src)
  case result of
    Left (err::IOException) -> tell $ "Error loading script at " ++ show src ++ ":\n" ++ show err
    Right (Left parseErr) -> tell $  "Parse error reading " ++ show src ++ "; " ++ show parseErr
    Right (Right (parsedHtml,_)) -> do
      parsedStmts <- liftIO $ getPageJavaScript parsedHtml
      dynamicJavaScriptLoader ct parsedStmts
                   
onDemandJavaScriptFromFile ct sp = do
  let src = unStringPatForOnDemandJavaScript sp
  -- Now, for some real input/output (and not simple mutation).  Bye bye functional programming.
  result <- liftIO $ try (parseJavaScriptFromFile src)
  case result of
    Left (err::IOException) -> tell $ "Error loading script at " ++ show src ++ ":\n" ++ show err
    Right parsedStmts -> dynamicJavaScriptLoader ct parsedStmts
      
    
-- |It is safe to 'newValue ... cxt'.
builtinDispatch :: (MonadIO m)
                => [Char]
                -> Contour
                -> [(Label,Contour)]
                -> (Label,Contour)
                -> CfaT Value (StateT (JsCFAState Contour) m) ()
builtinDispatch "Object" ct _ cxt = do
  newObject cxt []
  return ()
builtinDispatch "eval" ct _ cxt = do
  warn "trivial eval definition"
  newString cxt SAny
  return ()
builtinDispatch "Array" ct (this:_) cxt = do
  newArray cxt []
  return ()
builtinDispatch "Array.concat" ct args@(this:rest) cxt = do
  arr@(AObject{aObjectProps=arrSet}) <- newArray cxt []
  -- this implementation breaks ordering
  let copy src = propagateTo src cxt $ \val -> case val of
        AObject {aObjectX=PArray,aObjectProps=props} -> propagateTo props arrSet $ \propVal -> case propVal of
            AProperty id (ValueSet vals) -> propagateProperty cxt arrSet id $ \vals' -> subsetOf vals vals'
            otherwise -> warn $ "not a property: " ++ show propVal
        otherwise -> warn $ "arbitrary flattening at " ++ show cxt ++ "; possible conflation"
  let flatten src = propagateProperty cxt arrSet "0" $ \propSet -> flow1 src propSet $ \v -> 
                      if isAbstractArray v then Nothing else Just v
  mapM_ copy args
  mapM_ flatten args
-- builtinDispatch "Array.length" ct (this ..
builtinDispatch "Array.push" ct (this:arg:_) cxt = do
  propagateTo this cxt $ \val -> case val of
    AObject{aObjectProps=props,aObjectX=PArray} -> propagateTo arg props $ \argVal -> do
        -- we increment ix for each incoming value!
        flow1 arg props (\_ -> Nothing) -- artificial dependency creation, since we have to increment stuff
        ix' <- currentSetSize props
        let ix = ix' - 4 -- 4 things in the array prototype
        let set = primeSet cxt ix
        newValue argVal set
        newValue (AProperty (show ix) (ValueSet set)) props -- SAFE?
    otherwise ->
      warnAt ("Array.push applied to " ++ show val) (show ct)
builtinDispatch "Array.slice" ct [this,begin] cxt = do
  propagateTo this cxt $ \obj -> case obj of
    AObject{aObjectProps=ixs,aObjectX=PArray} -> do
      AObject{aObjectProps=destIxs} <- newArray cxt [] -- each source array maps to a unique destination
      propagateTo begin cxt $ \begin_ix -> case begin_ix of
        ANum x -> do let ix_min = truncate x
                     flow1 ixs destIxs $ \prop -> case prop of
                       AProperty id (ValueSet vals) -> case tryInt id of
                         Just ix | ix >= ix_min -> Just $ AProperty (show $ ix - ix_min) (ValueSet vals)
                                 | otherwise    -> Nothing
                         Nothing -> Nothing
                       otherwise -> Nothing
        otherwise -> flow1 ixs destIxs $ \prop -> case prop of
          AProperty id (ValueSet vals) -> case tryInt id of
            Just ix -> Just prop
            Nothing -> Nothing
          otherwise -> Nothing
    otherwise -> warn $ "Array.slice at " ++ show cxt ++ " applied to " ++ show obj
builtinDispatch "Array.slice" ct [this,begin,end] cxt = do
  propagateTo this cxt $ \obj -> case obj of
    AObject{aObjectProps=ixs,aObjectX=PArray} -> do
      AObject{aObjectProps=destIxs} <- newArray cxt [] -- each source array maps to a unique destination
      propagateTo begin cxt $ \begin_ix -> propagateTo end cxt $ \end_ix -> case (begin_ix,end_ix) of
        (ANum x,ANum y) -> do 
          let ix_min = truncate x
          let ix_max = truncate y
          flow1 ixs destIxs $ \prop -> case prop of
            AProperty id (ValueSet vals) -> case tryInt id of
              Just ix | ix >= ix_min && ix < ix_max -> Just $ AProperty (show $ ix - ix_min) (ValueSet vals)
                      | otherwise -> Nothing
              Nothing -> Nothing
            otherwise -> Nothing
        otherwise -> flow1 ixs destIxs $ \prop -> case prop of
          AProperty id (ValueSet vals) -> case tryInt id of
            Just ix -> Just prop
            Nothing -> Nothing
          otherwise -> Nothing
    otherwise -> warn $ "Array.slice at " ++ show cxt ++ " applied to " ++ show obj
-- .apply with no arguments.
builtinDispatch "Function.apply" ct [thisFn,thisObj] cxt = do
  application thisFn [thisObj] ct cxt
  propagateTo thisFn cxt $ \val -> case closureThis val of
    Just thisLbl -> subsetOf thisObj (thisLbl,ct)
    Nothing -> return ()
builtinDispatch "Function.apply" ct (thisFn:thisObj:arg:_) cxt = do
  JsCFAState { jscfaOpts = opts } <- lift get
  let expSrcs = cfaOptUnlimitedRecursion opts
  -- applicationHook <- callHook thisFn [] ct cxt
  let app formals results ce = do
        let formalsCount = (length formals) - 2
        -- this flows into the first formal
        subsetOf thisObj (formals !! 0)
        -- construct the arguments array (second formal)
        arguments <- newArray cxt []
        newValue arguments (formals !! 1) -- TODO: safe?
        -- the arguments are in an array (an object really)
        propagateTo arg cxt $ \argVal -> case argVal of
          AObject{aObjectProps=props,aObjectX=PArray} -> do
            propagateTo props cxt $ \elemVal -> case elemVal of
              AProperty id (ValueSet vals) -> do
                case tryInt id of
                  Just ix -> 
                    if ix < formalsCount
                      then do newValue elemVal (formals !! 1) -- TODO: safe?
                              subsetOf vals (formals !! (ix + 2))
                      else return () -- warn $ "argument out of bound: " ++ id
                  -- arrays have various builtins that are not copied over. This
                  -- drops user-defined non-indexable properties too, but that
                  -- should be okay.
                  Nothing -> return ()
              otherwise ->
                warn $ "non-object argument (1): " ++ show elemVal
          otherwise ->
            warn $ "illegal argument to Function.apply: " ++ show argVal
        mapM_ (\set -> subsetOf set cxt) results
  propagateTo thisFn cxt $ \fnVal -> case fnVal of
    AFunction{aFunctionLabel=fnLbl} | fnLbl `elem` callStack ct && (not $ isRecursionAllowed expSrcs fnLbl) -> do
      warn $ "ignoring .apply: " ++ show fnLbl ++ " at " ++ show (fst cxt)
      return ()
    AFunction{aFunctionLabel=fnLbl,aFunctionArgs=fnArgs,
              aFunctionLocals=fnLocals,aFunctionEnv=ceClosure,
              aFunctionBody=(EqualOrd body)} -> do
{- #ifdef  TRACE_APPLICATION
      warn $ "applying " ++ show fnLbl ++ " from " ++ show (callStack ct)
               ++ " in " ++ show ct
#endif -}
      let formals = map (\lbl -> (lbl,ct)) fnArgs
      let locals  = map (\lbl -> (lbl,ct)) fnLocals
      let ce = M.union (M.fromList (formals ++ locals)) ceClosure
      results <- {-applicationHook fnVal-} (stmt ce (newCall fnLbl ct) body)
      app formals results ce
    otherwise ->
      warn $ "non-function value: " ++ show fnVal
  return ()
builtinDispatch "addEventListener" ct (this:evtType:listener:_) cxt = do
  newString cxt SAny -- cxt.1
  let result = primeSet cxt 2
  -- TODO: It's okay to use the contour ct since contours are abstract and don't represent any particular relationship
  -- between calls--for now.  However, it is a total hack, and we really need different kinds of top-level contours.
  -- asyncHook ct this cxt (application listener [primeSet cxt 1] ct result) False
  -- state@(JsCFAState{jscfasFinalFlows=fs}) <- lift get
  -- lift $ put state{jscfasFinalFlows = (AnyString,arg):fs}
  return ()
builtinDispatch "document.write" ct [this,html] cxt@(lbl,_) = do
  warn $ "document.write ..."
  let sourceName = case labelSource lbl of { Just s -> s ; Nothing -> "<dynamic>" }
  propagateTo html cxt $ \html -> case html of
    AObject{aObjectX=(PString sp)} -> onDemandJavaScript ct sp sourceName
    otherwise -> warn $ "document.write applied to " ++ show html ++ " at " ++ show cxt
builtinDispatch "Element" ct [this,tag] cxt@(lbl,_) = do
  let sourceName = case labelSource lbl of { Just s -> s ; Nothing -> "<dynamic>" }
  -- Programmatically, the only way to access an element is using one of the document.getElement* methods, or with
  -- an element object.
  -- If this is a <script> element, we have to load the script.  Currently, we only handle scripts that reference
  -- external files (i.e. the src attribute).
  propagateTo tag cxt $ \tag -> case tag of
    AObject{aObjectX=(PString sp)} | lowercase (unStringPatForOnDemandJavaScript sp) ==  "script"  ->
      propagateProperty this cxt "src" $ \srcSet -> propagateTo srcSet cxt $ \src -> case src of
        AObject{aObjectX=(PString sp)} -> onDemandJavaScriptFromFile ct sp
        otherwise -> warn $ "builtinDispatch [" ++ show ct ++ "] : src property of a <script> tag assigned to " 
                            ++ show src
    AObject{aObjectX=(PString sp)} | lowercase (unStringPatForOnDemandJavaScript sp) ==  "iframe"  ->
      propagateProperty this cxt "src" $ \srcSet -> propagateTo srcSet cxt $ \src -> case src of
        AObject{aObjectX=(PString sp)} -> dynamicIFrameLoader ct sp
        otherwise -> warn $ "builtinDispatch [" ++ show ct ++ "] : src property of an <iframe> tag assigned to " 
                            ++ show src
    otherwise -> return ()
  -- If the innerHTML attribute is assigned to, we parse it and load any JavaScript it contains.
  JsCFAState {jscfasBuiltins=builtins} <- lift get
  unsafePropagateProperty this cxt "innerHTML" $ \htmlSet -> propagateTo htmlSet cxt $ \html -> case html of
    AObject{aObjectX=(PString sp)} -> onDemandJavaScript ct sp sourceName
    UndefinedVal -> return ()
    otherwise -> warn $ "Element.innerHTML assigned to " ++ show html ++ " at " ++ show htmlSet
builtinDispatch "XMLHttpRequest" ct (this:_) cxt = do
  -- nothing to initialize
  return () 
builtinDispatch "XMLHttpRequest.open" ct [this,method,url] cxt = do
{- #ifdef  DEBUG_XHR
  warn $ "(XMLHttpRequest) this.open"
  propagateTo url cxt $ \val -> warn $ "(XMLHttpRequest) this.url = " ++ show val
#endif -}
  propagateProperty this cxt "url" $ \urlSet -> subsetOf url urlSet
  return ()
builtinDispatch "XMLHttpRequest.open" ct [this,method,url,async] cxt = do
  warnAt "dropping async argument to XHR.open" (show ct) 
  builtinDispatch "XMLHttpRequest.open" ct [this,method,url] cxt
--
-- XMLHttpRequest.prototype.send
--
builtinDispatch "XMLHttpRequest.send" ct (this:contentArg:_) cxt = do
{- #ifdef  DEBUG_XHR
  warn $ "(XMLHttpRequest) this.send in " ++ show ct
#endif -}
  let result = primeSet cxt 1
  let handlerSet = primeSet cxt 2
  -- set XMLHttpRequest.content
  propagateProperty this contentArg "content" $ \contentProp -> subsetOf contentArg contentProp 
  -- flow a server value into responseText
  unsafePropagateProperty this cxt "responseText" $ \responseText -> do
    let svrSet = primeSet responseText 1
    newValue (AServerVal svrSet) responseText -- acceptable use of newValue
  -- the asynchronous application
  -- asyncHook ct this cxt (application handlerSet [] ct result) True
  -- populate the set of handler functions
  propagateProperty this handlerSet "onreadystatechange" $ \rst -> subsetOf rst handlerSet
builtinDispatch "String.any" ct [this] cxt = do
  newString cxt SAny
  return ()
builtinDispatch "print" ct [this,val] cxt = do
  propagateTo val cxt $ \v -> do
    -- tell $ "----------------------------"
    tell $ show v
    tell $ "At: " ++ show ct
    {- srcs <- sources val
    tell $ "Sources:"
    mapM_ (tell.show) srcs
    tell $ "----------------------------" -}
  newValue UndefinedVal cxt -- acceptable use of newValue
builtinDispatch "$A" ct [this,valStx] stx = do
  propagateTo valStx stx $ \val -> case objectProperties val of
    Nothing -> do
      newArray stx []
      return ()
    Just propSet -> propagatePropertyOf val stx "toArray" $ \propValSet -> propagate propValSet $ \propVal -> 
      case propVal of
        -- toArray is not defined
        UndefinedVal -> do
          AObject{aObjectProps=ixs} <- newArray stx []
          flow1 propSet ixs $ \property -> case property of
            AProperty propId _ | isJust (tryInt propId) -> Just property
                               | otherwise -> Nothing
            otherwise -> error "$A: non-property value in a property set"
        AFunction{aFunctionThis=thisLbl} -> do
          subsetOf this (thisLbl,ct)
          application propValSet [] ct stx
        otherwise -> warn $ "$A: expected function or undefined in .toArray: " ++ show propVal
builtinDispatch "$w" ct [this,valStx] stx = do
  propagateTo valStx stx $ \val -> case val of
    AObject{aObjectX=(PString sp)} -> case unStringPat sp of
      Just s -> do
        stringPrototype <- builtinPrototype "String"
        let mk (s,ix) = do
              let set = primeSet stx ix
              newValue (AObject (fst set) set (PString $ SConst s)) set
              return set
        strs <- mapM mk (zip (L.words s) [2..]) -- newArray uses 1
        newArray stx strs
        return ()
      Nothing -> warn $ "$w applied to strange string at " ++ show stx ++ "; argument was " ++ show val
    otherwise -> 
      warn $ "$w applied to non-string at " ++ show stx ++ "; argument was " ++ show val
      
builtinDispatch name ct args _ = do
  warn $ "ERROR: non-existant builtin or pattern-match failure`" ++ name 
            ++ "'; " ++ show (length args) ++ " arguments, call from " ++ show ct

initialize :: (MonadIO m)
           => CfaT Value (StateT (JsCFAState Contour) m) ()
initialize = do
  JsCFAState {jscfasBuiltins=builtins} <- lift get
  ctArray <- emptyContour
  -- Whenever window.location is assigned to, create a navigate node off the
  -- page.
  case M.lookup "window" builtins of
    Just lbl -> do
      let windowSet = (lbl,topContour)
      unsafePropagateProperty windowSet windowSet "location" $ \locSet -> 
        return () -- propagate locSet navigateHook
    Nothing -> fail "initialize: could not find window"
