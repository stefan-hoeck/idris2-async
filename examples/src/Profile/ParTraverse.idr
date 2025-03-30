module Profile.ParTraverse

import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-par-traverse FIBERS 

  Spawns `FIBERS` number of fibers via `parTraverse` runs them asynchronously
  printing the average time spent per fiber. This is a microbenchmark
  for testing the cost of spawning and running fibers in parallel.
  """

parameters {auto has : Has Errno es}
  
  export
  measure : Nat -> Prog es ()
  measure n = do
    dur <- delta (ignore $ parTraverse pure [0..n] >>= pure . maybe 0 sum)
    stdoutLn (prettyNS $ toNano dur `div` cast n)

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [i] = do
    iters <- readOptIO ONat i
    measure iters
  prog _ = throw (WrongArgs usage)
