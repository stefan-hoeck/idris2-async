module Profile.Race

import Data.Linear.Deferred
import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-race TYPE FIBERS 

  Sequentially runs `FIBERS` number of races, of type `TYPE` (see below)
  and computes the average time taken for each race to run to completion.

  The following types of races can be run:

    * trivial: The race is between `never` and `pure n`, both of which
      need not be scheduled on the event loop.
    * single: The race is between `never` and `pure () $> n`, the first
      of which will not be scheduled on the event loop while the second will.
    * both: The race is between `pure () >> never` and `pure () $> n`, both
      of which will be scheduled on the event loop.
  """

parameters {auto has : Has Errno es}
  iterate : Nat -> Nat -> (Nat -> Prog es Nat) -> Prog es ()
  iterate tot 0     f = prntLn tot
  iterate tot (S k) f = f k >>= \v => iterate (tot+v) k f

  run : String -> Nat -> Prog es ()
  run "trivial" n = iterate 0 n $ \x => race2 never (pure x) id id 0
  run "single"  n = iterate 0 n $ \x => race2 never (pure () $> x) id id 0
  run _         n = iterate 0 n $ \x => race2 (pure () >> never) (pure () $> x) id id 0

  measure : String -> Nat -> Prog es ()
  measure tpe n = do
    dur <- delta (run tpe n)
    stdoutLn (prettyNS $ toNano dur `div` cast n)

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [tpe,i] = do
    iters <- readOptIO ONat i
    measure tpe iters
  prog _ = throw (WrongArgs usage)
