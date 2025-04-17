module IO.Async.Core

import Data.Linear.Unique
import public Control.Monad.MCancel
import public Data.Linear.ELift1

%default total

public export
0 IOToken : Type
IOToken = Token World

public export
0 Callback : List Type -> Type -> Type
Callback es a = Outcome es a -> IO1 ()

||| A fiber is a series of computations that will be run
||| in strict sequence and will eventually terminate
||| with a result of type `Outcome es a`: It will either
||| produce a result of type `a`, an error of type `HSum es`,
||| or - in case it was canceled early - end with `Canceled`.
|||
||| From the outside, a fiber can be observed by installing 
||| a callback, which will be invoked as soon as the fiber has
||| terminated with a result.
|||
||| In addition, a running fiber can be canceled, so that it
||| aborts all computations at soon as possible. Canceling a fiber
||| that has already completed is a no-op.
public export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  cancel_  : IO1 ()
  observe_ : IOToken -> Callback es a -> IO1 (IO1 ())

||| Sum-type describing the computation running on a fiber.
|||
||| `Async` can be thought of a powerful alternative to `IO`
||| that comes with error handling, capabilities for
||| spawning additional `Async` computations (each running
||| on its of `Fiber`), plus the ability for being canceled
||| (from the inside or from other fibers).
|||
||| In order to *run* an `Async` computation, we an
||| `IO.Async.Loop.EventLoop`, which takes care of running
||| many fibers (each of which might spawn additional fibers)
||| concurrently. Some event loops will even offer true parallelism,
||| distributing the fibers to be run across several operating
||| system threads.
public export
data Async : (e : Type) -> (es : List Type) -> Type -> Type where
  ||| Implements bind (`>>=`)
  Bind   : Async e es a -> (a -> Async e es b) -> Async e es b

  ||| A pure result
  Val    : a -> Async e es a

  ||| An error
  Err    : HSum es -> Async e es a

  ||| A wrapped synchronous/blocking IO action
  Sync   : IO (Result es a) -> Async e es a

  ||| Cancels the curret fiber
  Cancel : Async e es ()

  ||| Run the given cancel hook when cancelation is observed for `act`
  OnCncl : (act : Async e es a) -> (hook : Async e [] ()) -> Async e es a

  ||| Masks a fiber as uncanceble
  ||| This takes a function argument which will get the running fiber's
  ||| identifier token plus cancelation id in order to unmask certain
  ||| inner regions, where cancellation can again be observed.
  ||| See also `Poll`.
  UC     : (IOToken -> Nat -> Async e es a) -> Async e es a

  ||| Error handling: In case an error occured, it is wrapped in
  ||| a `Left`, while a successful result is wrapped in a `Right`.
  ||| Note, that we do not handle the `Canceled` case: Cancellation
  ||| cannot be undone. In can be temporarily masked using `UC`, but
  ||| after that, it will be observed as soon as possible.
  Attempt : Async e es a -> Async e fs (Result es a)

  ||| Returns the context currently handling this fiber, giving us access
  ||| to functionality specific to the running event loop.
  Env  : Async e es e

  ||| Returns the current fiber's unique identifier
  Self : Async e es IOToken

  ||| Cedes control to the execution context
  ||| Fibers are auto-ceded after a predefined number of evaluation steps
  ||| to make sure other fibers get a chance to run even when the event loop
  ||| is single-threaded. In addition, a fiber can make room for other
  ||| fibers by invoking `cede` at strategic points.
  Cede : Async e es ()

  ||| Runs the given computation concurrently to this one returning a
  ||| `Fiber` representing the runnign computation.
  Start : Async e es a -> Async e fs (Fiber es a)

  ||| The asynchronous primitive. This allows us to register callbacks
  ||| and await their invocation, thus blocking the current fiber until
  ||| a result is ready. Being able to treat this as a regular
  ||| IO-like computation is one of the main reasons why `Async` is such
  ||| a powerful abstraction.
  ||| 
  ||| The `IO1 ()` returned after installing a callback will be treated
  ||| as a cancellation hook: It will be invoked if the current
  ||| computation is canceled and cancellation can currently be observed.
  ||| 
  ||| We use this data constructor whenever we'd like to wait for a
  ||| result to be ready at a later time such as a timer, input from
  ||| a pipe or socket, or data available from standard input.
  Asnc   : ((Result es a -> IO1 ()) -> IO1 (IO1 ())) -> Async e es a

  ||| Temporarily undo a layer of uncancelability. See also `UC`.
  APoll  : IOToken -> Nat -> Async e es a -> Async e es a

--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

||| Lifts a pure `Result` into `Async`.
export %inline
terminal : Result es a -> Async e es a
terminal = either Err Val

||| Lifts an effectful `Result` into `Async`.
export %inline
sync : IO (Result es a) -> Async e es a
sync = Sync

||| Asynchronous FFI: Wraps a callback handler into `Async`.
|||
||| The `IO1 ()` action returned after registering the callback will
||| be used for cancelation and cleanup.
export %inline
primAsync : ((Result es a -> IO1 ()) -> IO1 (IO1 ())) -> Async e es a
primAsync = Asnc

||| Starts a new fiber, running it concurrently to the current one
export %inline
start : Async e es a -> Async e fs (Fiber es a)
start = Start

||| Cedes control back to the execution context.
export %inline
cede : Async e es ()
cede = Cede

||| Returns the environment provided by the event loop this
||| fiber is currently running in.
export %inline
env : Async e es e
env = Env

||| Returns this fiber's unique identifier.
export %inline
self : Async e es IOToken
self = Self

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
MErr (Async e) where
  fail          = Err
  attempt       = Attempt
  bind          = Bind
  succeed       = Val
  mapImpl f v   = Bind v (Val . f)
  appImpl ff fv = Bind ff (`mapImpl` fv)

export %inline
HasIO (Async e es) where
  liftIO = sync . map Right

export %inline
MCancel (Async e) where
  onCancel = OnCncl
  canceled = Cancel
  uncancelable f = UC $ \t,n => f (APoll t n)

export %inline
ELift1 World (Async e) where
  elift1 act = sync $ runIO $ \t => toResult (act t)
