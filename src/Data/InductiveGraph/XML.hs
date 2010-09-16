module Data.InductiveGraph.XML
  ( xmlGraph
  , writeGraphML
  ) where

import System.IO (hPutStrLn)
import Text.XML.HaXml.XmlContent hiding (content)
import Text.XML.HaXml.TypeMapping
import Text.XML.HaXml.Pretty (document,content)
import Text.PrettyPrint.HughesPJ (render)
import Text.XML.HaXml
import Data.InductiveGraph.Class

instance HTypeable a => HTypeable (Vertex a) where
  toHType _ = Prim "HAsk" "XML"

instance XmlContent a => XmlContent (Vertex a) where
  toContents (Vertex ix val to) = vertex : edges where
    vertex  = CElem (Elem "node" [("id",str2attr (show ix))] (toContents val)) ()
    edges = map (\vx' -> mkEdge (vxIx vx')) to
    mkEdge ix2 = CElem
      (Elem "edge" [("source",str2attr (show ix)),("target",str2attr (show ix2))] []) ()
      
      
xmlGraph vxs = graph where 
  graph = 
    CElem (Elem "graph" 
                [("id",str2attr "Graph"),("edgedefault",str2attr "directed")] 
                [graphml]) ()
  graphml = CElem (Elem "graphml" [] (preface ++ (toContents vxs))) ()
  preface = 
    [ CElem (Elem "key" [("id",str2attr "label"),("for",str2attr "node"),
                         ("attr.name",str2attr "label"),
                         ("attr.type",str2attr "string")] []) ()
    , CElem (Elem "key" [("id",str2attr "type"),("for",str2attr "node"),
                         ("attr.name",str2attr "type"),
                         ("attr.type",str2attr "integer")] []) ()
    ]

writeGraphML handle vxs = 
  hPutStrLn handle $ render (content (xmlGraph vxs))
