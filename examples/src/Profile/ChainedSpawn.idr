module Profile.ChainedSpawn

import IO.Async.Deferred
import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-chained-spawn FIBERS 

  Sequentially spawns `FIBERS` number of fibers and runs them asynchronously
  printing the average time spent per fiber. This is a microbenchmark
  for testing the cost of spawning and running fibers sequentially.
  """

parameters {auto has : Has Errno es}
  iterate : Deferred1 () -> Nat -> Prog es ()
  iterate def 0     = put1 def ()
  iterate def (S k) = do
    pure ()
    ignore $ start (iterate def k)

  spawn : Nat -> Prog es ()
  spawn n = do
    def <- deferred1Of ()
    _   <- start $ iterate def n
    await1 def

  measure : Nat -> Prog es ()
  measure n = do
    dur <- delta (spawn n)
    stdoutLn (prettyNS $ toNano dur `div` cast n)

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [i] = do
    iters <- readOptIO ONat i
    measure iters
  prog _ = throw (WrongArgs usage)
