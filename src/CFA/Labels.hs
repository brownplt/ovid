-- |Set labels for control flow analysis.
module CFA.Labels (Label (..)
  , buildLabels, buildLabels', isBuiltinLabel,
  labelSource, labelPos, labelName,primeLabel, labelSources
  , unsafeLabelIx,deconstructLabel,propLabel) where

import Data.Generics
import Text.ParserCombinators.Parsec.Pos (SourcePos,sourceLine,sourceColumn,
  initialPos,sourceName)
import Control.Monad.Trans
import Data.Maybe (fromJust,isJust)
import Data.List (intersperse,groupBy,concatMap)

import Framework


-- | Labels identify sources and are built compositionally. 
data Label 
  = PrimedLabel Label Int -- ^a label indexed by a unique number
  | SourceLabel (Maybe SourcePos) (Maybe String) Int -- ^a label representing a source location
  | IdLabel Label String -- ^usually used for properties 
  | IxLabel Int
  deriving (Typeable,Data,Eq,Ord)

labelPos :: Label -> Maybe SourcePos
labelPos (SourceLabel (Just p) _ _) = Just p
labelPos _ = Nothing

labelSource :: Label -> Maybe String
labelSource lbl = case labelPos lbl of
  Just p -> Just (sourceName p)
  Nothing -> Nothing
  
  
unsafeLabelIx (IxLabel ix) = Just ix
unsafeLabelIx (PrimedLabel _ ix) = Just ix
unsafeLabelIx (SourceLabel _ _ ix) = Just ix
unsafeLabelIx _ = Nothing

labelName :: Label -> Maybe String
labelName (SourceLabel _ (Just id) _) = Just id
labelName _ = Nothing

labelSources :: Label -> [SourcePos]
labelSources lbl = everything (++) (mkQ [] (\pos -> [pos])) lbl

deconstructLabel :: Label -> [Label]
deconstructLabel lbl = everything (++) (mkQ [] id) lbl
  
-- ---------------------------------------------------------------------------------------------------------------------
-- Printing

showSrc :: SourcePos -> Bool -> String
showSrc pos showLoc = name ++ show (sourceLine pos) ++ ":" ++ show (sourceColumn pos) where
  name = if showLoc then sourceName pos ++ ":" else ""

instance Show Label where
  show (SourceLabel (Just pos) (Just id) _) = id ++ ":" ++ (showSrc pos False)
  show (SourceLabel (Just pos) Nothing _) = showSrc pos True
  show (SourceLabel Nothing (Just id) _) = id
  show (IdLabel lbl id) = show lbl ++ ":" ++ id
  show (SourceLabel _ _ _) = error "Label.show : illegal SourceLabel"
  show (IxLabel ix) = "{" ++ show ix ++ "}"
  show (PrimedLabel lbl n) = show lbl ++ "." ++ show n

-- ---------------------------------------------------------------------------------------------------------------------
-- Constructing labels


primeLabel :: Label -> Int -> Label
primeLabel lbl ix = PrimedLabel lbl ix  


propLabel :: Label -> String -> Label
propLabel lbl id = IdLabel lbl id

-- ---------------------------------------------------------------------------------------------------------------------
-- Miscellaneous

isBuiltinLabel (SourceLabel Nothing (Just _) _) = True
isBuiltinLabel _ = False

buildLabels :: Monad m => CounterT m a -> m a
buildLabels = evalCounter

-- |Builds labels that are distinct from all labels ' <= init'
buildLabels' :: Monad m => Counter -> CounterT m a -> m (a,Counter)
buildLabels' init m = runCounter init m

