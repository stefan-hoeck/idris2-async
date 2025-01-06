||| Utilities for working with work loops.
module IO.Async.Internal.Loop

import Data.So
import IO.Async.Internal.Concurrent
import IO.Async.Internal.Ref
import System.Clock
import System

%default total

||| Used in several loop implementation.
|||
||| A loop running on its own thread will ask for more work.
||| In case of work available, it will process it, otherwise
||| the loop will wait until it is notified that more work is
||| ready. If it gets a `Done`, it will terminate.
public export
data Work : Type where
  Done : Work
  W    : IO1 () -> Work

||| An empty work
export
dummy : IO1 ()
dummy = \t => () # t

||| `IO1` version of `die`
export %inline
die : String -> IO1 ()
die s = ioToF1 $ die s

||| An empty work package.
export %inline
noWork : IO1 Work
noWork t = W dummy # t

||| The `Done` work package.
export %inline
done : IO1 Work
done t = Done # t

||| Wraps a work package in a `IO1 Work`.
export %inline
work : IO1 () -> IO1 Work
work w t = W w # t

-- ||| This will wait on the give condition and return with `noWork`
-- ||| once it awakes. The calling loop will then be responsible to ask
-- ||| for more work.
-- export %inline
-- waitNoWork : Condition -> Mutex -> IO1 Work
-- waitNoWork c m w = let MkIORes _ w := conditionWait c m w in noWork w
-- 
-- ||| This will wait on the give condition with a timeout
-- ||| and return with `noWork` once it awakes. The calling loop
-- ||| will then be responsible to ask for more work.
-- export %inline
-- sleepNoWork : Condition -> Mutex -> Integer -> IO1 Work
-- sleepNoWork c m us w =
--   let MkIORes _ w := conditionWaitTimeout c m us w
--    in noWork w

||| Tail-recursively runs a list of `IO1` actions
export
runAll : (a -> IO1 ()) -> List a -> IO1 ()
runAll f []        t = () # t
runAll f (x :: xs) t = let _ # t := f x t in runAll f xs t

||| Keep only those values in a list that have not yet been canceled.
export
nonCanceled : (a -> IORef Bool) -> List a -> IO1 (List a)
nonCanceled f = go [<]

  where
    go : SnocList a -> List a -> IO1 (List a)
    go sx []        t = (sx <>> []) # t
    go sx (x :: xs) t =
      case read1 (f x) t of
        True  # t => go sx xs t
        False # t => go (sx :< x) xs t

||| Sleeps for the given duration (rounded down to micro seconds)
export
doSleep : Clock Duration -> IO1 ()
doSleep c t =
  let v := cast {to = Int} (toNano c `div` 1000)
   in case choose (v >= 0) of
        Left x  => ioToF1 (usleep v) t
        Right x => () # t

||| Boolean-like flag indicating if a loop is still alive or should
||| stop.
public export
data Alive = Stop | Run
