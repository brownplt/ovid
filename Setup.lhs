#!/usr/bin/env runhaskell
> import Distribution.Simple
> import System.Cmd

> testHook args isB desc build = do
>   putStrLn "Running graph tests..."
>   _ <- system "/usr/bin/env runhaskell testdata/data/InductiveGraphTests.hs"
>   return ()


> main = defaultMainWithHooks (simpleUserHooks { runTests = testHook })
