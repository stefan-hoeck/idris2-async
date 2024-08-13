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
  W    : PrimIO () -> Work

||| An empty work
export
primDummy : PrimIO ()
primDummy = \w => MkIORes () w

||| `PrimIO` version of `die`
export %inline
primDie : String -> PrimIO ()
primDie s = toPrim $ die s

export %inline
primWhen : Bool -> PrimIO () -> PrimIO ()
primWhen True  f = f
primWhen False _ = MkIORes ()

||| An empty work package.
export %inline
noWork : PrimIO Work
noWork = MkIORes (W primDummy)

||| The `Done` work package.
export %inline
done : PrimIO Work
done = MkIORes Done

||| Wraps a work package in a `PrimIO Work`.
export %inline
work : PrimIO () -> PrimIO Work
work w = MkIORes (W w)

||| This will wait on the give condition and return with `noWork`
||| once it awakes. The calling loop will then be responsible to ask
||| for more work.
export %inline
waitNoWork : Condition -> Mutex -> PrimIO Work
waitNoWork c m w = let MkIORes _ w := conditionWait c m w in noWork w

||| This will wait on the give condition with a timeout
||| and return with `noWork` once it awakes. The calling loop
||| will then be responsible to ask for more work.
export %inline
sleepNoWork : Condition -> Mutex -> Integer -> PrimIO Work
sleepNoWork c m us w =
  let MkIORes _ w := conditionWaitTimeout c m us w
   in noWork w

||| Tail-recursively runs a list of `PrimIO` actions
export
runAll : (a -> PrimIO ()) -> List a -> PrimIO ()
runAll f []        w = MkIORes () w
runAll f (x :: xs) w = let MkIORes _ w := f x w in runAll f xs w

||| Keep only those values in a list that have not yet been canceled.
export
nonCanceled : (a -> Ref Bool) -> List a -> PrimIO (List a)
nonCanceled f = go [<]

  where
    go : SnocList a -> List a -> PrimIO (List a)
    go sx []        w = MkIORes (sx <>> []) w
    go sx (x :: xs) w =
      let MkIORes b w := readRef (f x) w
       in case b of
            True  => go sx xs w
            False => go (sx :< x) xs w

||| Sleeps for the given duration (rounded down to micro seconds)
export
doSleep : Clock Duration -> PrimIO ()
doSleep c w =
  let v := cast {to = Int} (toNano c `div` 1000)
   in case choose (v >= 0) of
        Left x  => toPrim (usleep v) w
        Right x => MkIORes () w

||| Boolean-like flag indicating if a loop is still alive or should
||| stop.
public export
data Alive = Stop | Run
