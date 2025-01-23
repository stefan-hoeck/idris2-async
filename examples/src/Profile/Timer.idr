module Profile.Timer

import System.Clock
import Opts

%default total

usage : String
usage =
  """
  Usage: async-examples profile-timer DUR ITER 

  Repeatedly (`ITER` iterations) sleeps for `DUR` micro seconds and
  computes the average time spent sleeping to get an idea of the
  overhead taken for generating and tearing down the timers.
  """

pretty : Integer -> String
pretty n = "\{secs}\{msecs}\{usecs}"
  where
    secs, msecs, usecs : String
    secs =
      case n `div` 1_000_000_000 of
        0 => ""
        s => "\{show s} s "

    msecs =
      case n `div` 1_000_000 of
        0 => ""
        s => "\{show $ s `mod` 1000} ms "

    usecs =
      case n `div` 1_000 of
        s => "\{show $ s `mod` 1000} us"

parameters {auto has : Has Errno es}
  
  measure : (ns : Integer) -> Clock Duration -> Nat -> Nat -> Prog es ()
  measure ns cl c 0     = stdoutLn (pretty $ ns `div` cast c)
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
