||| Utilities for working with work loops.
module IO.Async.Loop

import Data.Nat
import Data.Linear.Deferred
import Data.Linear.Unique

import public IO.Async.Core
import public Data.Linear.Ref1
import Syntax.T1

%default total

--------------------------------------------------------------------------------
-- Fiber Implementation
--------------------------------------------------------------------------------

record FiberImpl (es : List Type) (a : Type) where
  constructor FI
  ||| Unique identifier of the fiber
  token  : IOToken

  ||| Set, if the fiber has been canceled.
  cncl   : Once World ()

  ||| Set, if the fiber has run to completion.
  res    : Deferred World (Outcome es a)

-- allocates a new fiber
newFiber : IO1 (FiberImpl es a)
newFiber t =
  let tok  # t := Unique.token1 t
      cncl # t := onceOf1 () t
      res  # t := deferredOf1 (Outcome es a) t
   in FI tok cncl res # t

toFiber : FiberImpl es a -> Fiber es a
toFiber fbr = MkFiber (putOnce1 fbr.cncl ()) (observeDeferredAs1 fbr.res)

--------------------------------------------------------------------------------
-- Running Fiber State
--------------------------------------------------------------------------------

-- An item on the call stack of a running fiber. See `Stack`.
data StackItem : (e : Type) -> (es,fs : List Type) -> (a,b : Type) -> Type where 
  -- A monadic continuation. This is put on the call stack whenever we
  -- encounter the `Bind` data constructor.
  Bnd   : (a -> Async e es b) -> StackItem e es es a b

  -- Error handling. This is put on the call stack whenever we encounter
  -- the `Attempt` data constructor.
  Att   : StackItem e es fs a (Result es a)

  -- Instruction to increase the cancelation mask by one.
  Inc   : StackItem e es es a a

  -- Utility to inform us that the computation is finished here.
  Abort : StackItem e [] es () a

  -- Instruction to decrease the cancelation mask by one.
  Dec   : StackItem e es es a a

  -- A cancelation hook. This will be ignored if the fiber is
  -- currently not canceled or cancelation cannot be observed.
  Hook  : Async e [] () -> StackItem e es es a a

-- Properly typed stack of nested `Bind`s plus instructions
-- related to cancelation and masking of a running fiber.
--
-- While building and consuming our own call stack comes with a certain
-- overhead, this overhead is typically small compared to the cost
-- associated with spawning fibers, performing system calls, or
-- handling asynchronous boundaries.
data Stack : (e : Type) -> (es,fs : List Type) -> (a,b : Type) -> Type where
  Nil  : Stack e es es a a
  (::) : StackItem e es fs a b -> Stack e fs gs b c -> Stack e es gs a c

||| Internal state of a running fiber.
export
record FbrState (e : Type) where
  constructor FST
  {0 curErrs, resErrs : List Type}
  {0 curType, resType : Type}

  fiber : FiberImpl resErrs resType -- (mutable) state of the running fiber
  mask  : Nat -- cancellation mask
  comp  : Async e curErrs curType -- current computation
  stack : Stack e curErrs resErrs curType resType -- computation stack

||| Result of (partially) evaluate a fiber.
public export
data RunRes : Type -> Type where
  ||| The fiber has terminated with an `Outcome`, or we arrived at
  ||| an asynchronous boundary (`Asnc` data constructor) and the
  ||| fiber should be parked until a result is ready.
  Done : RunRes e

  ||| Evaluation of the fiber is not yet finished, but should be
  ||| rescheduled by moving the fiber at the end of the event loop's
  ||| work queue. This happens a) after a certain number of evaluation
  ||| steps, or b) when `cede` is encountered.
  Cont : FbrState e -> RunRes e

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
interface EventLoop (0 e : Type) where
  constructor EL
  ||| Submits a fiber to be run by event loop `el`
  spawn : (el : e) -> FbrState e -> IO1 ()

  ||| Number of evaluation steps before a fiber should be rescheduled.
  limit : Nat

export
runFbr : (el : EventLoop e) => e -> FbrState e -> IO1 (RunRes e)

export
runAsyncWith :
     {auto el : EventLoop e}
  -> e
  -> Async e es a
  -> (Outcome es a -> IO ())
  -> IO ()
runAsyncWith env act cb = runIO $ \t =>
  let fbr # t := newFiber t
      _   # t := observeDeferredAs1 fbr.res fbr.token (\o => ioToF1 $ cb o) t
   in spawn env (FST fbr 0 act []) t

export %inline
runAsync : EventLoop e => e -> Async e es a -> IO ()
runAsync env as = runAsyncWith env as (\_ => pure ())

--------------------------------------------------------------------------------
-- Async Runner (Here be Dragons)
--------------------------------------------------------------------------------

record CBState (es : List Type) (a : Type) where
  constructor CST
  {0 resErrs : List Type}
  {0 envType, resType : Type}

  env      : envType
  cnclCB   : IO1 ()
  cnclCncl : IO1 ()
  fiber    : FiberImpl resErrs resType
  mask     : Nat -- cancellation mask
  stack    : Stack envType es resErrs a resType
  {auto el : EventLoop envType}

prepend : Async e [] a -> Stack e [] fs a b -> Stack e [] fs () b
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
%noinline
asynchronous : ((Result es a -> IO1 ()) -> IO1 (IO1 ())) -> IO1 (Fiber es a)
asynchronous install t =
  let def     # t := deferredOf1 (Outcome es a) t
      cleanup # t := install (putDeferred1 def . toOutcome) t
      cncl        := T1.do cleanup; putDeferred1 def Canceled
   in MkFiber cncl (observeDeferredAs1 def) # t

%noinline
spawnCB : CBState es a -> Outcome es a -> IO1 ()
spawnCB (CST env c1 c2 fbr cm st) o t =
  case o of
    Succeeded r => let _ # t := c2 t in spawn env (FST fbr cm (Val r) st) t
    Error     x => let _ # t := c2 t in spawn env (FST fbr cm (Err x) st) t
    Canceled    => let _ # t := c1 t in spawn env (FST fbr 1  (Val ()) (hooks st)) t

%noinline
writeOnCB :
     Once World (Outcome es a)
  -> ((Result es a -> IO1 ()) -> IO1 (IO1 ()))
  -> IO1 (IO1 ())
writeOnCB o f t = f (putOnce1 o . toOutcome) t

%noinline
obsOnce : Once World (Outcome es a) -> CBState es a -> IO1 (RunRes e)
obsOnce o st t = let _ # t := observeOnce1 o (spawnCB st) t in Done # t

-- Finalize the fiber with the given outcome and call all its observers.
%inline
finalize : FiberImpl es a -> Outcome es a -> IO1 (RunRes e)
finalize fbr o t = let _ # t := putDeferred1 fbr.res o t in Done # t

-- Invokes runR or runC depending on if the fiber has
-- been canceled and cancelation is currently observable
run :
     {auto el : EventLoop e}
  -> (env : e)           -- the event loop on which the fiber runs
  -> Async e es a        -- next computation step of the running fiber
  -> (cancelMask  : Nat) -- 0 if cancelation can be observed > 0 otherwise
  -> (cedeCount   : Nat) -- if at 0, the fiber will be rescheduled
  -> FiberImpl fs b      -- mutable state of the running fiber
  -> Stack e es fs a b   -- call stack of the running fiber
  -> IO1 (RunRes e)

-- evaluates an alive fiber: one that has not been canceled or
-- for which cancelation can currently not be observed
runR :
     {auto el : EventLoop e}
  -> (env : e)
  -> Async e es a
  -> (cancelMask  : Nat)
  -> (cedeCount   : Nat)
  -> FiberImpl fs b
  -> Stack e es fs a b
  -> IO1 (RunRes e)

-- runs a canceled fiber
-- we no longer need a `cancelMask` argument, because all we
-- are going to do now is extract and run the cancellation hooks
runC :
     {auto el : EventLoop e}
  -> (env : e)
  -> Async e es a
  -> (cedeCount : Nat)
  -> FiberImpl fs b
  -> Stack e es fs a b
  -> IO1 (RunRes e)

-- the cede count arrived at 0 so we stop and allow the fiber
-- to be rescheduled on the event loop
run env act cm 0     fbr st t = Cont (FST fbr cm act st) # t

-- the cancel mask is at 0 so cancelation can currently be observed
-- we check if the fiber has been canceled and either invoke
-- `runC` or `runR`
run env act 0  (S k) fbr st t =
  case completedOnce1 fbr.cncl t of
    False # t => runR env act 0 k fbr st t
    True  # t => runC env act k fbr st t

-- cancellation can currently not be observed so there is no
-- point in checking if the fiber has been canceled.
run env act c  (S k) fbr st t = runR env act c k fbr st t

runC env act cc fbr st t =
  case act of
    UC f   => run env (f fbr.token 1) 1 cc fbr (Dec::st) t
    Val x => case st of
      Bnd f :: tl => case f x of
        UC g => run env (g fbr.token 1) 1 cc fbr (Dec::tl) t
        a    => run env (pure ()) 1 cc fbr (hooks st) t
      Att :: tl   => runC env (Val $ Right x) cc fbr tl t
      Inc :: tl   => run env (Val x) 1 cc fbr tl t
      _           => run env (pure ()) 1 cc fbr (hooks st) t
    Err x => case st of
      Att :: tl => runC env (Val $ Left x) cc fbr tl t
      Inc :: tl => run env (Err x) 1 cc fbr tl t
      _         => run env (pure ()) 1 cc fbr (hooks st) t
    _    => run env (pure ()) 1 cc fbr (hooks st) t

runR env act cm cc fbr st t =
  case act of
    Bind x f => case x of
      Val x => run env (f x) cm cc fbr st t
      Self  => run env (f fbr.token) cm cc fbr st t
      _     => run env x cm cc fbr (Bnd f :: st) t

    Val x      => case st of
      Bnd f  :: tl => run env (f x) cm        cc fbr tl t
      Inc    :: tl => run env act   (S cm)    cc fbr tl t
      Dec    :: tl => run env act   (pred cm) cc fbr tl t
      -- ignore cancel hook because cancelation is currently not
      -- observable.
      Hook h :: tl => run env act   cm        cc fbr tl t
      Abort  :: tl => finalize fbr Canceled t
      Att    :: tl => run env (Val $ Right x) cm cc fbr tl t
      []          => finalize fbr (Succeeded x) t

    Err x      => case st of
      Att    :: tl => run env (Val $ Left x) cm cc fbr tl t
      Bnd _  :: tl => run env (Err x)        cm cc fbr tl t
      Inc    :: tl => run env act   (S cm)      cc fbr tl t
      Dec    :: tl => run env act   (pred cm)   cc fbr tl t
      -- ignore cancel hook because cancelation is currently not
      -- observable.
      Hook h :: tl => run env act   cm        cc fbr tl t
      Abort  :: tl => finalize fbr Canceled t
      []          => finalize fbr (Error x) t

    -- For certain fibers it is not necessary to actually spawn them
    -- on the event loop, so we optimize those away.
    Start x     => case x of
      Asnc reg =>
        let f2 # t := asynchronous reg t
         in run env (Val f2) cm cc fbr st t
      Cancel => run env (Val $ synchronous Canceled) cm cc fbr st t
      Val v  => run env (Val $ synchronous (Succeeded v)) cm cc fbr st t
      Err x  => run env (Val $ synchronous (Error x)) cm cc fbr st t
      Self   => run env (Val $ synchronous (Succeeded fbr.token)) cm cc fbr st t
      _ =>
        let fbr2 # t := newFiber t
            _    # t := spawn env (FST fbr2 0 x []) t
         in run env (Val $ toFiber fbr2) cm cc fbr st t

    Sync x      =>
      let r # t := ioToF1 x t
       in run env (terminal r) cm cc fbr st t

    Attempt x => run env x cm cc fbr (Att :: st) t

    Cancel      => 
      let _ # t := putOnce1 fbr.cncl () t
       in run env (Val ()) cm cc fbr st t

    OnCncl x y  => run env x cm cc fbr (Hook y :: st) t

    UC f        => run env (f fbr.token (S cm)) (S cm) cc fbr (Dec::st) t

    Env         => run env (Val env) cm cc fbr st t

    Cede        => Cont (FST fbr cm (Val ()) st) # t

    Self        => run env (Val fbr.token) cm cc fbr st t

    Asnc f =>
      let o  # t := onceOf1 (Outcome es a) t
          c1 # t := writeOnCB o f t
          c2 # t := observeCancel o cm fbr t
       in case peekOnce1 o t of
            Nothing  # t => obsOnce o (CST env c1 c2 fbr cm st) t
            Just out # t => case out of
              Succeeded r => let _ # t := c2 t in run env (Val r) cm cc fbr st t
              Error     x => let _ # t := c2 t in run env (Err x) cm cc fbr st t
              Canceled    => let _ # t := c1 t in run env (pure ()) 1 cc fbr (hooks st) t

    APoll tok k x => case tok == fbr.token && k == cm of
      True  => run env x (pred cm) cc fbr (Inc :: st) t
      False => run env x cm        cc fbr st t

runFbr env (FST fbr msk act st) = run env act msk (limit @{el}) fbr st
