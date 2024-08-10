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

--------------------------------------------------------------------------------
-- Event Loop
--------------------------------------------------------------------------------

||| Initial work package sent to an event loop.
|||
||| Most work will be run on one of the worker threads of a thread pool,
||| so this provides a way for the worker to inform the work package how
||| to cede itself to later execuption. This allows us to evaluate a single
||| fiber mostly on one thread even in the face of (auto)-ceding.
public export
record Package (e : Type) where
  constructor Pkg
  env : Ref e
  act : PrimIO ()

||| A context for submitting and running work packages asynchronously.
|||
||| The basic functionality of an event loop is to allow us to spawn
||| new work packages, all of which will then be run concurrently (but not
||| necessarily in parallel), and to `cede` a running computation, so that
||| it will be processed later while allowing other work packages to be
||| processed first.
|||
||| In addition, an event loop can support arbitrary additional effects, for
||| instance, the ability to setup timers, signal handlers, and asynchronous
||| `IO` actions. These additional capabilities are represented by type
||| parameter `e`, representing the event loop currently processing a work
||| package.
public export
record EventLoop (e : Type) where
  constructor EC
  spawn : Package e -> PrimIO ()
  cede  : e -> PrimIO () -> PrimIO ()
  init  : e
