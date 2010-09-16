-- |Interactions with the user.
module Ovid.Interactions 
  ( tell
  , options
  ) where

import Ovid.Prelude
import qualified System.Console.Editline.Readline as R

-- |Prompt the user.
tell s = liftIO (putStrLn s)

-- |Asks the user to pick an item from a list.
options :: (MonadIO m, Show a) => [a] -> m a
options xs = do
  let numOptions = length xs
  let showOption (n,x) = tell $ show n ++ " - " ++ show x
  mapM_ showOption (zip [1..] xs)
  tell $ "Select one (1 .. " ++ show numOptions ++ ") >"
  let makeSelection = do
        ch <- liftIO $ R.readKey
        case tryInt "ch" of
          Nothing -> do 
            tell $ "Enter a number between 1 and " ++ show numOptions
            makeSelection        
          Just n -> 
            if n >= 1 && n <= numOptions 
              then return (xs !! (n-1))
              else do
                tell $ "Enter a number between 1 and " ++ show numOptions
                makeSelection
  makeSelection
        
