module Profile.Async2

import Data.Linear.Deferred
import Opts
import Profile.Util
import System.Clock

%default total

usage : String
usage =
  """
  Usage: async-examples profile-async2 iterations
  """

parameters {auto has : Has Errno es}


  single : Nat -> Prog es ()
  single n = do
    o <- lift1 (onceOf1 Nat)
    f <- start {es = []} (lift1 $ putOnce1 o n)
    ignore $ primAsync (\cb => observeOnce1 o (cb . Right))
  
  asyncs : Nat -> Prog es ()
  asyncs 0     = pure ()
  asyncs (S k) = do
    single k
    asyncs k
  
  export
  measure : Nat -> Prog es ()
  measure n = do
    dur <- delta (asyncs n)
    stdoutLn (prettyNS $ toNano dur `div` cast n)

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [i] = do
    iters <- readOptIO ONat i
    measure iters
  prog _ = throw (WrongArgs usage)
