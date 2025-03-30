module Profile.Alloc

import Data.Array
import Opts
import Profile.Util

%default total

usage : String
usage =
  """
  Usage: async-examples profile-alloc

  Spawns one million fibers, some of which iterate rapidly, simulating
  a typical scatter gather pattern.
  """

allocation : Nat -> Array Nat
allocation n = A _ $ generate (max 100 (min n 2000)) cast

res : Outcome es a -> Maybe a
res (Succeeded x) = Just x
res _             = Nothing

parameters {auto has : Has Errno es}

  fiber : Nat -> Prog es Nat
  fiber i = Prelude.do
    cede
    arr <- pure (allocation i)
    cede
    _   <- pure (sum arr)
    if i > 1000
       then cede $> i
       else cede >> fiber (assert_smaller i (S i))

  run : Prog es Nat
  run = do
    fs <- traverse (\_ => start $ fiber 0) [0 .. pred 2500]
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
