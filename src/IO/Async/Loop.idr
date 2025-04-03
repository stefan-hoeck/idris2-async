||| Utilities for working with work loops.
module IO.Async.Loop

import Data.Linear.Deferred
import Data.Linear.Unique

import public IO.Async.Core
import public Data.Linear.Ref1
import Syntax.T1

%default total

--------------------------------------------------------------------------------
-- Fiber Implementation (Here be Dragons)
--------------------------------------------------------------------------------

record FiberImpl (es : List Type) (a : Type) where
  constructor FI
  ||| Unique identifier of the fiber
  token  : IOToken

  ||| Set, if the fiber has been canceled.
  cncl   : Once World ()

  ||| Set, if the fiber has run to completion.
  res    : Deferred World (Outcome es a)

-- allocates a new fiber, setting its initial state to `Running`
newFiber : IO1 (FiberImpl es a)
newFiber t =
  let tok  # t := Unique.token1 t
      cncl # t := onceOf1 () t
      res  # t := deferredOf1 (Outcome es a) t
   in FI tok cncl res # t

-- Finalize the fiber with the given outcome and call all its observers.
%inline
finalize : FiberImpl es a -> Outcome es a -> IO1 ()
finalize fbr o = putDeferred1 fbr.res o

toFiber : FiberImpl es a -> Fiber es a
toFiber fbr = MkFiber (putOnce1 fbr.cncl ()) (observeDeferredAs1 fbr.res)

--------------------------------------------------------------------------------
-- Running Fiber State
--------------------------------------------------------------------------------

data StackItem : (e : Type) -> (es,fs : List Type) -> (a,b : Type) -> Type where 
  Bnd   : (Result es a -> Async e fs b) -> StackItem e es fs a b
  Inc   : StackItem e es es a a
  Abort : StackItem e [] es () a
  Dec   : StackItem e es es a a
  Hook  : Async e [] () -> StackItem e es es a a

-- Properly typed stack of nested `Bind`s plus instructions
-- related to cancelation and masking
data Stack : (e : Type) -> (es,fs : List Type) -> (a,b : Type) -> Type where
  Nil  : Stack e es es a a
  (::) : StackItem e es fs a b -> Stack e fs gs b c -> Stack e es gs a c

export
record FbrState (e : Type) where
  constructor FST
  {0 curErrs, resErrs : List Type}
  {0 curType, resType : Type}

  env   : e
  fiber : FiberImpl resErrs resType
  mask  : Nat -- cancellation mask
  comp  : Async e curErrs curType -- current computation
  stack : Stack e curErrs resErrs curType resType -- computation stack

public export
data RunRes : Type -> Type where
  Done : RunRes e
  Cont : FbrState e -> RunRes e

export
runFbr : FbrState e -> IO1 (RunRes e)

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
  spawn : FbrState e -> IO1 ()

--------------------------------------------------------------------------------
-- Async Runner (Here be Dragons)
--------------------------------------------------------------------------------

prepend : Async e es a -> Stack e es fs a b -> Stack e [] fs () b
prepend act s = Bnd (const act) :: s

hooks : Stack e es fs a b -> Stack e [] fs () b
hooks (Hook h :: t) = prepend h (hooks t)
hooks (_ :: t)      = hooks t
hooks []            = [Abort]

observeCancel : Once World (Outcome es a) -> Nat -> FiberImpl fs b -> IO1 (IO1 ())
observeCancel o 0 f = observeOnce1 f.cncl (\_ => putOnce1 o Canceled)
observeCancel _ _ _ = (unit1 #)

-- a fiber that has already completed with the given result.
synchronous : Outcome es a -> Fiber es a
synchronous o = MkFiber unit1 (\_,cb,t => let _ # t := cb o t in unit1 # t)

-- a fiber from an asynchronous computation.
asynchronous : ((Result es a -> IO1 ()) -> IO1 (IO1 ())) -> IO1 (Fiber es a)
asynchronous install t =
  let def     # t := deferredOf1 (Outcome es a) t
      cleanup # t := install (putDeferred1 def . toOutcome) t
      cncl        := T1.do cleanup; putDeferred1 def Canceled
   in MkFiber cncl (observeDeferredAs1 def) # t


-- Invokes runR or runC depending on if the fiber has
-- been canceled and cancelation is currently observable
covering
run :
     EventLoop e
  -> (env : e)
  -> Async e es a
  -> (cancelMask  : Nat)
  -> (cedeCount   : Nat)
  -> FiberImpl fs b
  -> Stack e es fs a b
  -> IO1 (RunRes e)

covering
runR :
     EventLoop e
  -> (env : e)
  -> Async e es a
  -> (cancelMask  : Nat)
  -> (cedeCount   : Nat)
  -> FiberImpl fs b
  -> Stack e es fs a b
  -> IO1 (RunRes e)

covering
runC :
     EventLoop e
  -> (env : e)
  -> Async e es a
  -> (cedeCount : Nat)
  -> FiberImpl fs b
  -> Stack e es fs a b
  -> IO1 (RunRes e)
