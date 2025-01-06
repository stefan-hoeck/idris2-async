||| Utilities for working with work loops.
module IO.Async.Loop

import public Data.Linear.Ref1

%default total

public export
0 IO1 : Type -> Type
IO1 = F1 [World]

||| Initial work package sent to an event loop.
|||
||| Most work will be run on one of the worker threads of a thread pool,
||| so this provides a way for the worker to inform the work package how
||| to cede itself to later execuption. This allows us to evaluate a single
||| fiber mostly on one thread even in the face of (auto)-ceding.
public export
record Package (e : Type) where
  constructor Pkg
  env : IORef e
  act : IO1 ()

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
  constructor EL
  spawn : Package e -> IO1 ()
  cede  : Package e -> IO1 ()
  init  : e
