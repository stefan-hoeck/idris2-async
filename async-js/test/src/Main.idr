module Main

import IO.Async.JS
import Test.Async.Cancel
import Test.Async.Core
import Test.Async.Race
import Test.Async.Spec

%default total

%foreign "javascript:lambda:(a,ms,val,w) => new Promise((f) => setTimeout(() => f(val(w)), Number(ms)))"
prim__delayed : Nat -> PrimIO a -> PrimIO (Promise a)

%foreign "javascript:lambda:(a,ms,msg,w) => new Promise((f,g) => setTimeout(() => g(new Error (msg))))"
prim__delayedErr : Nat -> String -> PrimIO (Promise a)

delayed : HasIO io => Nat -> Lazy a -> io (Promise a)
delayed n v = primIO (prim__delayed n $ \w => MkIORes v w)

delayedErr : HasIO io => Nat -> String -> io (Promise a)
delayedErr n msg = primIO (prim__delayedErr n msg)

prog : Async JS [JSErr] ()
prog = do
  weakenErrors $ runTree $ 
    Node "Async Spec"
      [ Core.specs
      , Cancel.specs
      , Race.specs
      ]
  -- sequencing of timeouts
  sleep 200.ms
  putStrLn "slept for 200 ms"
  sleep 1.s
  putStrLn "slept for 1 s"

  -- running timeouts in parallel
  fbs <- for [1..10] $ \i =>
    start {es = []} (sleep 1.s >> putStrLn "Fiber \{show i} done.")
  traverse_ wait fbs

  -- cancellation of long running jobs
  longRunning <- start {es = []} (putStrLn "long running job" >> sleep 10000.s)
  fastRunning <- start {es = []} (putStrLn "no, stop!" >> sleep 1.s >> cancel longRunning)
  wait longRunning
  wait fastRunning

  -- awaiting a promise.
  putStrLn "Now, let's make a Promise."
  s <- delayed 1000 "hello from a promise" >>= promise
  putStrLn "Message: \{s}"
  putStrLn "Now, let's make a failed Promise."
  s <- delayedErr {a = String} 1000 "this didn't work" >>= promise
  putStrLn "I'll never arrive here: \{s}"

covering
main : IO ()
main = app (handle [\x => putStrLn "Oh no! (\{dispErr x})"]  prog)
