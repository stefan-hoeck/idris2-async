module Profile.Spawn

import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-spawn FIBERS 

  Spawns `FIBERS` number of fibers and runs them asynchronously
  printing the average time spent per fiber. This is a microbenchmark
  for testing the cost of spawning and running fibers in parallel.
  """

parameters {auto has : Has Errno es}
  
  spawn : Nat -> Prog es ()
  spawn 0     = pure ()
  spawn (S k) = do
    f <- start (the (Prog es ()) (pure ()))
    spawn k
    ignore (join f)

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

