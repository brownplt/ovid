module Test.Environment where

import Environment

type Id = String
type MyEnv  = Env Id Int

e1 = local "x" 5 >> global "y" 10

e2 :: EnvM Id Int ()
e2 = nest (return ()) return

e3 = nest (local "x" 10) return

--e2 = nest (local "y" 7) (\_ -> return ())

e15 =
  nest (local "y" 55  >> getEnv >>= \env -> local "x" 33 >> (return env)) return

run e = putStr $ show (build e) ++ "\n"
  
  
main = do
  run e1
  run e2
  --run e15
