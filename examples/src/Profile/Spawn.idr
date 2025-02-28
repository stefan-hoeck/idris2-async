module Profile.Spawn

import Data.Linear.Deferred
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
  effect : IORef Nat -> Once World () -> Prog es ()
  effect ref def = do
    b <- runIO (casupdate1 ref (\x => (pred x, x==1)))
    when b (putOnce def ())

  spawn : Nat -> Prog es ()
  spawn n = do
    def <- onceOf ()
    ref <- newref n
    repeat n (start $ effect ref def)
    awaitOnce def

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

