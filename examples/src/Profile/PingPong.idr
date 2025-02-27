module Profile.PingPong

import IO.Async.BQueue
import IO.Async.Deferred
import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-ping-pong ITER 

  Sequentially runs `ITER` number of iterations and computes
  the average time per bind operation. This is a microbenchmark
  for testing the cost per iteration in the fiber evaluation
  loop.
  """

parameters {auto has : Has Errno es}
  
  effect : Deferred1 () -> BQueue () -> IORef Nat -> Prog es ()
  effect def q ref = do
    _ <- start (enqueue {es} q ())
    dequeue q
    1 <- update ref (\x => (pred x, x)) | _ => pure ()
    put1 def ()

  iterate : Nat -> Prog es ()
  iterate n = do
    def <- deferred1Of ()
    ref <- newref n
    q   <- bqueueOf () 1
    _   <- start $ repeat {es} n (start $ effect def q ref)
    await1 def
    

  measure : Nat -> Prog es ()
  measure n = do
    dur <- delta (iterate n)
    stdoutLn (prettyNS $ toNano dur `div` cast n)

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [i] = do
    iters <- readOptIO ONat i
    measure iters
  prog _ = throw (WrongArgs usage)

