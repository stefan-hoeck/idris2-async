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
||| in strict sequence that will eventually terminate
||| with a result of type `Outcome es a`: It will either
||| produce a result of type `a`, an error of type `HSum es`,
||| or - in case it was canceled early - end with `Canceled`.
|||
||| From the outside, a fiber can be observed by installing 
||| a callback, which will be invoked as soon as the fiber has
||| terminated with a result.
|||
||| In addition, a running fiber can be canceled, so that it
||| aborts all computations at soon as possible. Canceled a fiber
||| that has already completed is a no-op.
public export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  cancel_  : IO1 ()
  observe_ : IOToken -> Callback es a -> IO1 (IO1 ())

export
data Async : (e : Type) -> (es : List Type) -> Type -> Type where
  -- Implements bind (`>>=`)
  Bind   : Async e es a -> (a -> Async e es b) -> Async e es b

  -- A pure result (value or error)
  Val    : a -> Async e es a

  -- A pure result (value or error)
  Err    : HSum es -> Async e es a

  -- A wrapped synchronous/blocking IO action
  Sync   : IO (Result es a) -> Async e es a

  -- Cancels the curret fiber
  Cancel : Async e es ()

  -- Run the given cancel hook when cancelation is observed
  -- for `act`
  OnCncl : (act : Async e es a) -> (hook : Async e [] ()) -> Async e es a

  -- Masks a fiber as uncanceble
  UC     : (IOToken -> Nat -> Async e es a) -> Async e es a

  Attempt : Async e es a -> Async e fs (Result es a)

  -- Returns the context currently handling this fiber, giving us access
  -- to functionality specific to the running event loop.
  Env  : Async e es e

  -- Returns the current fiber's token
  Self : Async e es IOToken

  -- Cedes control to the execution context
  Cede : Async e es ()

  Start : Async e es a -> Async e fs (Fiber es a)

  Asnc   : ((Result es a -> IO1 ()) -> IO1 (IO1 ())) -> Async e es a

  -- Temporarily undo a layer of uncancelability
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

export %inline
env : Async e es e
env = Env

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
