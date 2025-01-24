module Profile.Bind

import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-bind ITER 

  Sequentially runs `ITER` number of iterations and computes
  the average time per bind operation. This is a microbenchmark
  for testing the cost per iteration in the fiber evaluation
  loop.
  """

parameters {auto has : Has Errno es}
  
  binds : Nat -> Prog es ()
  binds 0     = pure ()
  binds (S k) = pure () >> binds k

  measure : Nat -> Prog es ()
  measure n = do
    dur <- delta (binds n)
    stdoutLn (prettyNS $ toNano dur `div` cast n)

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [i] = do
    iters <- readOptIO ONat i
    measure iters
  prog _ = throw (WrongArgs usage)

