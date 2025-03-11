module Profile.Consumers

import Opts
import Data.Linear.Deferred
import IO.Async.Channel
import Profile.Util
import System.Clock

usage : String
usage =
  """
  Usage: async-examples profile-consumers ITER 

  Let `ITER` producers produce `ITER` values and write them
  to a channel, from which a single consumer reads and counts
  the values.
  """

startEnd : (p1,p2 : Poll) -> String
startEnd p1 p2 = "Start: \{show $ threadId p1}; End: \{show $ threadId p2})"

parameters {auto has : Has Errno es}
           (c : Channel Nat)
           (d : Deferred World ())

  dosend : Nat -> Prog es ()
  dosend n = do
    _  <- race2 (await d) (sleep 10.ms >> send c n)
    pure ()

  fbrc : Nat -> Prog es ()
  fbrc n = traverse_ dosend [0 .. n]
  
  loopc : IORef Nat -> Prog es ()
  loopc r = do
    race [await d $> Just 0, receive c] >>= \case
      Just (Just n) => do
        mod r S
        loopc r
      _             => pure ()

measure : Has Errno es => Nat -> Prog es ()
measure n = do
  d <- deferredOf {s = World} ()
  c <- channelOf Nat 0
  f <- start (ignore (parTraverse (fbrc {es} c d) [0..n]) >> close c)
  r <- newref Z
  dur <- delta (loopc c d r)
  v <- readref r
  stdoutLn (prettyNS $ toNano dur `div` cast v)

export
prog : Has Errno es => Has ArgErr es => List String -> Prog es ()
prog ["--help"] = stdoutLn usage
prog [i] = do
  iters <- readOptIO ONat i
  measure iters
prog _ = throw (WrongArgs usage)
