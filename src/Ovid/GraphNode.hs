module Ovid.GraphNode (GraphNode (..), isRequestNode, isTopNode, isJoinNode, isAndNode, isOrNode, isExitNode,
  isEquivalentCall,nodeSet,isInternalNode,isDomEventNode, finalizeXHR, isDebugNode) where

import Text.XML.HaXml.XmlContent
import Text.XML.HaXml
import Data.InductiveGraph.XML
import Ovid.Prelude 
import qualified Data.Map as M
import Ovid.Abstraction
import CFA.Labels (Label,labelSource)
import CFA
import Scheme.Write

isInterestingNode v
  | isRequestNode v = "2"
  | isTopNode v = "1"
  | otherwise = "3"
 
isPageNavNode (PageNavNode{}) = True
isPageNavNode _                      = False
 
isRequestNode (ServerCallNode{}) = True
isRequestNode (ServerResponseNode{}) = True
isRequestNode (PageNavNode{}) = True
isRequestNode (RequestNode{}) = True
isRequestNode (ResponseNode{}) = True
isRequestNode _                  = False

isTopNode (TopNode{}) = True
isTopNode _         = False

isJoinNode (JoinNode{}) = True
isJoinNode _            = False

isExitNode (ClientReturnNode{}) = True
isExitNode _ = False

isAndNode (AndBranchNode{}) = True
isAndNode _           = False

isOrNode (OrBranchNode{}) = True
isOrNode _          = False

isDebugNode(DebugNode{}) = True
isDebugNode _ = False

-- Internal calls are calls that are inside a library that we cannot instrument.  We can instrument calls that are
-- entirely outside the library or calls that are at the boundary between the application and the library.
isInternalNode vx = case nodeSet vx of
  Nothing -> False
  Just (lbl,ct) -> case latestContext ct of
    Nothing -> False -- top-level call (how many of these are there?)
    Just cxt -> case labelSource cxt of
      Nothing -> True -- probably a builtin
      Just callSrc -> 
        if callSrc == "../flapjax/flapjax.js" 
          then case labelSource lbl of -- the calling function is in an internal library ...
            Just calledBlock -> calledBlock == "../flapjax/flapjax.js" -- ... so it is calling another internal?
            Nothing -> True -- ... its calling a builtin (that has no source)
          else
            False -- if it calling function is not in a library, we can instrument it


instance HTypeable GraphNode where
  toHType _ = Prim "HAsk" "XML"

finalizeXHR :: (MonadIO m) => (Cache Value) -> GraphNode -> m GraphNode
finalizeXHR r (ServerCallNode (EqualOrd urls) (EqualOrd contents) isRepeatable cxt) = do 
  let toUrlM (VObject{vObjectX=(PString sp)}) = return $ Just (unStringPat sp)
      toUrlM v = (warn $ "expected string for abstract url: " ++ show v) >> return Nothing
  urls <- liftM catMaybes (mapM toUrlM $ map (flattenValue r) urls)
  let contents' = map (flattenValue r) contents
  return $ RequestNode (EqualOrd urls) (EqualOrd contents') isRepeatable cxt
finalizeXHR r (ServerResponseNode (EqualOrd vals) cxt) = do
  return $ ResponseNode (EqualOrd $ map (flattenValue r) vals) cxt
finalizeXHR r (DebugNode "" set f) = do
  let vals = valuesOf r set
      s = concat (intersperse "\n" $ map write  (map (flattenValue r) vals)) 
  return $ DebugNode s set f
finalizeXHR _ node = return node


data GraphNode
  = ClientCallNode (Label,Contour)
  | ClientReturnNode (Label,Contour)
  | DomEventNode Int -- TODO: stupid hack
  -- |A request made to the server.  Representation during CFA, when the full value set is unknown.
  | ServerCallNode {  
      scnUrl :: EqualOrd [Value],
      scnContent :: EqualOrd [Value],
      scnIsRepeatable :: Bool,
      scnCxt :: (Label,Contour)
    }
  -- |A request made to the server.  Post-CFA representation of the abstract request, without any sets.
  | RequestNode {
      reqUrls :: EqualOrd [Maybe String], -- ^possibly indeterminate URL
      reqVals :: EqualOrd [RawValue],
      reqIsRepeatable :: Bool,
      reqCxt :: (Label,Contour)
    }
  -- |A response from the server.  Post-CFA representation.
  | ResponseNode {
      respVals :: EqualOrd [RawValue],
      respCxt :: (Label,Contour)
    }
  | ServerResponseNode {
      srnValues :: EqualOrd [Value],
      srnCxt :: (Label,Contour)
    }
  | AndBranchNode (Label,Contour)
  | OrBranchNode (Label,Contour)
  | JoinNode (Label,Contour)
  | TopNode { 
      vxTopSrc :: String -- ^name of the source of this graph
    }
  | PageNavNode {
      pageNavUrl :: String,
      pageNavCxt :: Int -- TODO: stupid hack, can break
    }
  | DebugNode {
      debugNodeString :: String, -- ^string displayed in the graph
      debugNodeArg :: (Label,Contour),
      debugNodeCxt :: (Label,Contour)
    }
  deriving (Ord,Eq)

isDomEventNode (DomEventNode{}) = True
isDomEventNode _ = False

nodeSet (ClientCallNode set) = Just set
nodeSet (ClientReturnNode set) = Just set
nodeSet _ = Nothing
  
-- |True if the two nodes have the same label.
isEquivalentCall :: GraphNode -> GraphNode -> Bool
isEquivalentCall (ClientCallNode (lbl1,_)) (ClientCallNode (lbl2,_)) = lbl1 == lbl2
isEquivalentCall (ClientReturnNode (lbl1,_)) (ClientReturnNode (lbl2,_)) = lbl1 == lbl2
isEquivalentCall (AndBranchNode (lbl1,_)) (AndBranchNode (lbl2,_)) = lbl1 == lbl2
isEquivalentCall (OrBranchNode (lbl1,_)) (OrBranchNode (lbl2,_)) = lbl1 == lbl2
isEquivalentCall (JoinNode (lbl1,_)) (JoinNode (lbl2,_)) = lbl1 == lbl2
isEquivalentCall _ _ = False -- page jumps and server calls are all unique
  
instance Show GraphNode where
  show (DebugNode str _ _) = "'(debug " ++ write str ++ ")"
  show (RequestNode (EqualOrd urls) (EqualOrd vals) isRepeatable _) =
    "'(request " ++ write isRepeatable ++ " " ++ write urls ++ " " ++ write vals ++ ")"
  show (ResponseNode (EqualOrd vals) _) =
    "'(response " ++ write vals ++ ")"
  show (PageNavNode {pageNavUrl=url}) =
    "'(jump-to " ++ write url ++ ")"
  show (JoinNode _) = "'join"
  show (AndBranchNode label) = "'and"
  show (OrBranchNode label)  = "'or"
  show (ServerCallNode{}) = "'(pre-request)"
  show (ServerResponseNode {}) = "'(pre-response)"
  show (ClientCallNode (lbl,ct)) = 
    "'(function " ++ show lbl ++ " " ++ show (show ct) ++ ")"
  show (ClientReturnNode (lbl,ct)) = 
    "'(return " ++ show (show lbl) ++ " " ++ show (show ct) ++ ")"
  show (TopNode{vxTopSrc=src}) = 
    "'(top " ++ write src ++ ")"
  show (DomEventNode{}) = "'(dom-event)"

nodeXmlWrapper color xs =
  [ CElem  (Elem "data" [("key",str2attr "label")] xs)  ()
  , CElem (Elem "data" [("key",str2attr "type")] [CString False color ()]) ()
  ]
  

showSet vx = case nodeSet vx of
  Nothing -> error "showSet: expected a node with an associated set"
  Just (lbl,ct) -> case latestContext ct of
    Nothing -> "<unknown>"
    Just callingLbl
      | labelSource callingLbl == (Just "../flapjax/flapjax.js") -> "I/" ++ (show lbl)
      | otherwise -> show callingLbl
    
instance XmlContent GraphNode where
  toContents vx@(DebugNode s _ _) = nodeXmlWrapper "2" [CString False s ()]
  toContents vx@(ClientCallNode set) = nodeXmlWrapper "3" [CString False ("E:" ++ (take 35 $ showSet vx)) ()]
  toContents vx@(ClientReturnNode set) = nodeXmlWrapper "3" [CString False ("X:" ++ (take 35 $ showSet vx)) ()]
  toContents vx@(DomEventNode{}) = nodeXmlWrapper "2" [CString False "DOM Event" ()]
  toContents node = nodeXmlWrapper (isInterestingNode node) [CString False (take 35 $ show node) ()] 

