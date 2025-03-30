module Profile.Scheduling

import IO.Async.BQueue
import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-scheduling

  Spawns one million fibers, some of which iterate rapidly, simulating
  a typical scatter gather pattern.
  """

res : Outcome es a -> Maybe a
res (Succeeded x) = Just x
res _             = Nothing

parameters {auto has : Has Errno es}

  fiber : Nat -> Prog es Nat
  fiber k = do
    cede
    j <- pure k
    cede
    if j > 10000
       then cede >> pure j
       else cede >> fiber (assert_smaller k $ S j)

  run : Prog es Nat
  run = do
    fs <- traverse (start . fiber) [0 .. 1_000_000]
    os <- traverse join fs
    pure $ sum (mapMaybe res os)

  export
  measure : Prog es ()
  measure = do
    dur <- delta (ignore run)
    stdoutLn (prettyNS $ toNano dur)

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [] = measure
  prog _  = throw (WrongArgs usage)
