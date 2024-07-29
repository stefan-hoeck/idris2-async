||| Utilities for working with work loops.
module IO.Async.Internal.Loop

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Ref

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

||| Boolean-like flag indicating if a loop is still alive or should
||| stop.
public export
data Alive = Stop | Run
