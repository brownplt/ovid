-- |Submit to the greater glory of Scheme.  Write Haskell values as 
-- Scheme-readable s-expressions.  They still have types, really.
module Scheme.Write
  ( Write (..)
  ) where

import Data.List (intersperse)

class Write t where
  write :: t -> String
  writeList :: [t] -> String -> String
  writeList [] s = "empty" ++ s
  writeList xs s = "(" ++ concat (intersperse " " (map write xs)) ++ ")" ++ s

instance Write Char where
  write ch = "#\\" ++ [ch]
  writeList str s = show str ++ s
  
instance Write Int where
  write n = show n
  
instance Write Double where
  write x = show x
  

instance Write Bool where
  write True = "#t"
  write False = "#f"
  
-- |'Nothing' is written as #f.
instance Write a => Write (Maybe a) where
  write Nothing = "#f"
  write (Just x) = write x

-- |Tuples are written as fixed-length lists.  
instance (Write a, Write b) => Write (a,b) where
  write (a,b) = "(" ++ write a ++ " " ++ write b ++ ")"

instance Write a => Write [a] where
  write a = writeList a ""
