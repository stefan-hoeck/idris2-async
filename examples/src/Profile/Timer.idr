module Profile.Timer

import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-timer DUR ITER 

  Repeatedly (`ITER` iterations) sleeps for `DUR` micro seconds and
  computes the average time spent sleeping to get an idea of the
  overhead taken for generating and tearing down the timers.
  """

parameters {auto has : Has Errno es}
  
  measure : (ns : Integer) -> Clock Duration -> Nat -> Nat -> Prog es ()
  measure ns cl c 0     = stdoutLn (prettyNS $ ns `div` cast c)
  measure ns cl c (S k) = do
    dur <- delta (sleep cl)
    measure (ns + toNano dur) cl c k

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [d,i] = do
    dur   <- readOptIO ONat d
    iters <- readOptIO ONat i
    measure 0 dur.us iters iters
  prog _ = throw (WrongArgs usage)
