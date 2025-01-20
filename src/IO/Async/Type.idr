module IO.Async.Type

import Data.Nat
import IO.Async.Loop
import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Token
import public IO.Async.Outcome

%default total

public export
0 Callback : List Type -> Type -> Type
Callback es a = Outcome es a -> IO1 ()

public export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  cancel_  : IO1 ()
  observe_ : Callback es a -> IO1 (Bool -> IO1 ())

export
data Async : (e : Type) -> (es : List Type) -> Type -> Type where
  -- Implements bind (`>>=`) and error handling
  Bind   : Async e es a -> (Result es a -> Async e fs b) -> Async e fs b

  -- A pure result (value or error)
  Term   : Result es a -> Async e es a

  -- A wrapped synchronous/blocking IO action
  Sync   : IO (Result es a) -> Async e es a

  -- Cancels the curret fiber
  Cancel : Async e es ()

  -- Run the given cancel hook when cancelation is observed
  -- for `act`
  OnCncl : (act : Async e es a) -> (hook : Async e [] ()) -> Async e es a

  -- Masks a fiber as uncanceble
  UC     : (Token -> Nat -> Async e es a) -> Async e es a

  -- Returns the context currently handling this fiber, giving us access
  -- to functionality specific to the running event loop.
  Env  : Async e es e

  -- Cedes control to the execution context
  Cede : Async e es ()

  Start : Async e es a -> Async e fs (Fiber es a)

  Asnc   : ((Result es a -> IO1 ()) -> IO1 (Bool -> IO1 ())) -> Async e es a

  -- Temporarily undo a layer of uncancelability
  APoll  : Token -> Nat -> Async e es a -> Async e es a

  -- Internal checking if asynchronous results are available.
  -- We only check after we have been notified that a result is ready.
  Wait : IORef (Maybe $ Result es a) -> Async e es a

--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

public export
0 Poll : Type -> Type
Poll e = forall es,a . Async e es a -> Async e es a

||| Lifts a pure `Result` into `Async`.
export %inline
terminal : Result es a -> Async e es a
terminal = Term

||| Lifts an effectful `Result` into `Async`.
export %inline
sync : IO (Result es a) -> Async e es a
sync = Sync

||| Primitive for implementing `(>>=)` and error handling
export %inline
bind : Async e es a -> (Result es a -> Async e fs b) -> Async e fs b
bind = Bind

||| Makes sure the given cancelation hook is run when `act` is canceled.
export %inline
onCancel : (act : Async e es a) -> (hook : Async e [] ()) -> Async e es a
onCancel = OnCncl

||| Gracefully cancels execution of the current fiber.
export %inline
canceled : Async e es ()
canceled = Cancel

||| Masks the given computation as *uncancelable* except for the regions
||| unmasked with the given `Poll`.
export %inline
uncancelable : (Poll e -> Async e es a) -> Async e es a
uncancelable f = UC $ \t,n => f (APoll t n)

||| Asynchronous FFI: Wraps a callback handler into `Async`.
|||
||| The `Bool -> IO1 ()` action returned after registering the callback will
||| be used for cancelation and cleanup. It is invoked with `True` in case
||| of cancelation and `False` in case of regular cleanup.
export %inline
primAsync : ((Result es a -> IO1 ()) -> IO1 (Bool -> IO1 ())) -> Async e es a
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

--------------------------------------------------------------------------------
-- Fiber Implementation (Here be Dragons)
--------------------------------------------------------------------------------

||| Lifts a value into `Async`.
export %inline
succeed : a -> Async e es a
succeed = terminal . Right

||| Lifts an error `Result` into `Async`.
export %inline
fail : HSum es -> Async e es a
fail = terminal . Left

export %inline
Functor (Async e es) where
  map f x = bind x $ terminal . map f

export %inline
Applicative (Async e es) where
  pure = succeed
  fa <*> ma = bind fa $ either fail (<$> ma)

export %inline
Monad (Async e es) where
  x >>= f = bind x (either fail f)

export %inline
HasIO (Async e es) where
  liftIO = sync . map Right

guaranteePrim : Async e es a -> (Bool -> IO1 ()) -> Async e es a
guaranteePrim fa fin =
  uncancelable $ \poll =>
    let finalized := onCancel (poll fa) (runIO $ fin True)
     in bind finalized $ \r => runIO (fin False) >> terminal r

--------------------------------------------------------------------------------
-- Fiber Implementation (Here be Dragons)
--------------------------------------------------------------------------------

%inline
emptyCBs : (0 es : _) -> (0 a : _) -> List (Token, Callback es a)
emptyCBs _ _ = []

-- State of a fiber
--
--   1) Running:   The fiber is currently being run in an execution context
--
--   2) Suspended: The fiber has been suspended because it is waiting for
--                 the result of an asynchronous computation. Once that is ready
--                 it can be resumed by invoking the given `IO1` action.
--
--   3) HasResult: The result of an asynchronous call is ready but the fiber
--                 is currently running. It should immediately continue upon
--                 being suspended. Note: The result might be from an outdated
--                 (canceled) asynchronous computation. In that case, the
--                 mutable reference holding the `Maybe` the value is waiting
--                 for will still return `Nothing`. That's no big deal, because
--                 the fiber will suspend itself again after an unsuccessful
--                 poll.
--
--   4) Done:      The fiber has terminated and produced the wrapped outcome.
data FiberState : (es : List Type) -> (a : Type) -> Type where
  Running   : FiberState es a
  Suspended : IO1 () -> FiberState es a
  HasResult : FiberState es a
  Done      : Outcome es a -> FiberState es a

-- State of a `Fiber`
record FiberST (es : List Type) (a : Type) where
  constructor FS
  ix       : Nat
  cbs      : List (Nat, Callback es a)
  canceled : Bool
  state    : FiberState es a

record FiberImpl (e : Type) (es : List Type) (a : Type) where
  constructor FI
  token  : Token
  env    : IORef e
  st     : IORef (FiberST es a)

-- allocates a new fiber, setting its initial state to `Running`
newFiber : TokenGen => EventLoop e -> IO1 (FiberImpl e es a)
newFiber el t =
  let tok  # t := Token.token t
      env  # t := refIO el.init t
      st   # t := refIO (FS 0 [] False Running) t
   in FI tok env st # t

-- remove the observer identified by the given token from the
-- list of callbacks.
stopObserving : Nat -> FiberImpl e es a -> Bool -> IO1 ()
stopObserving n fbr _ = casmod1 fbr.st {cbs $= filter ((n /=) . fst)}

-- Registeres a callback at a fiber
-- If the fiber has already terminated (it is in its `Done` state),
-- the callback is immediately invoked and no cancel hook provided.
-- Otherwise, the callback is given a unique identifier and added to
-- the fiber's list of callbacks. A cancel hook for removing the
-- observer is returned in this case.
observe : FiberImpl e es a -> Callback es a -> IO1 (Bool -> IO1 ())
observe fbr cb t =
  case casupdate1 fbr.st observeAct t of
    Left  act # t => let _ # t := act t in const dummy # t
    Right act # t => act # t
  where
    observeAct : FiberST es a -> (FiberST es a, (Either (IO1 ()) (Bool -> IO1 ())))
    observeAct s =
      case s.state of
        Done o => (s, Left $ cb o)
        _      =>
         let s2 := {ix $= S, cbs $= ((s.ix,cb)::)} s
          in (s2, Right $ stopObserving s.ix fbr)

-- Cede control to the physical thread this fiber is running on
cedeFbr : EventLoop e -> FiberImpl e es a -> IO1 () -> IO1 ()
cedeFbr el fbr act = el.cede (Pkg fbr.env act)

-- runs a list of callbacks
runCBs : List (Nat,Callback es a) -> Outcome es a -> IO1 ()
runCBs []             o t = () # t
runCBs ((_,cb) :: xs) o t = let _ # t := cb o t in runCBs xs o t

-- Finalize the fiber with the given outcome and call all its observers.
finalize : FiberImpl e es a -> Outcome es a -> IO1 ()
finalize fbr o t =
  let act # t := casupdate1 fbr.st finAct t
   in act t

  where
    finAct : FiberST es a -> (FiberST es a, IO1 ())
    finAct s = ({state := Done o, cbs := []} s, runCBs s.cbs o)

-- Cancel the given fiber, resuming its computation if it has
-- been suspended.
doCancel : FiberImpl e es a -> IO1 ()
doCancel fbr t =
  let act # t := casupdate1 fbr.st cancelAct t
   in act t

  where
    cancelAct : FiberST es a -> (FiberST es a, IO1 ())
    cancelAct s =
      case s.state of
        Done _        => (s,dummy)
        Suspended act => ({canceled := True, state := Running} s, act)
        _             => ({canceled := True} s, dummy)

-- Suspend the fiber because it is waiting for the result of
-- an asynchronous computation. If the asynchronous computation
-- was faster, the fiber's state will be at `HasResult` and
-- it will immediately be resumed.
suspend : FiberImpl e es a -> IO1 () -> IO1 ()
suspend fbr cont t =
  let act # t := casupdate1 fbr.st suspendAct t
   in act t

  where
    suspendAct : FiberST es a -> (FiberST es a, IO1 ())
    suspendAct s =
      case s.state of
        HasResult => ({state := Running} s, cont) 
        _         => ({state := Suspended cont} s, dummy) 

-- Resumes the computation of this fiber because the result from
-- an asynchronous computation is ready. If this is invoked while
-- the fiber is still running, we'll inform it that the result it
-- might be waiting for is ready, so that it will immediately
-- continue when it tries to suspend itself the next time.
--
-- If the fiber is already `Done`, well then we are much too late
-- and should abort silently.
resume : FiberImpl e es a -> IO1 ()
resume fbr t =
  let act # t := casupdate1 fbr.st resumeAct t
   in act t

  where
    resumeAct : FiberST es a -> (FiberST es a, IO1 ())
    resumeAct s =
      case s.state of
        Suspended c => ({state := Running} s, c)
        Running     => ({state := HasResult} s, dummy) 
        HasResult   => (s, dummy)
        Done _      => (s, dummy)

export
toFiber : FiberImpl e es a -> Fiber es a
toFiber fbr = MkFiber (doCancel fbr) (observe fbr)

--------------------------------------------------------------------------------
-- Async Runner (More Dragons)
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

prepend : Async e es a -> Stack e es fs a b -> Stack e [] fs () b
prepend act s = Bnd (const act) :: s

hooks : Stack e es fs a b -> Stack e [] fs () b
hooks (Hook h :: t) = prepend h (hooks t)
hooks (_ :: t)      = hooks t
hooks []            = [Abort]

parameters {auto tg : TokenGen}
           (limit   : Nat)

  -- Invokes runR or runC depending on if the fiber has
  -- been canceled and cancelation is currently observable
  covering
  run :
       EventLoop e
    -> Async e es a
    -> (cancelMask  : Nat)
    -> (cedeCount   : Nat)
    -> FiberImpl e fs b
    -> Stack e es fs a b
    -> IO1 ()

  covering
  runC :
       EventLoop e
    -> Async e es a
    -> (cedeCount : Nat)
    -> FiberImpl e fs b
    -> Stack e es fs a b
    -> IO1 ()

  covering
  runR :
       EventLoop e
    -> Async e es a
    -> (cancelMask  : Nat)
    -> (cedeCount   : Nat)
    -> FiberImpl e fs b
    -> Stack e es fs a b
    -> IO1 ()

  covering
  spawnFib : EventLoop e -> FiberImpl e es a -> Async e es a -> IO1 ()
  spawnFib el f act = el.spawn (Pkg f.env (run el act 0 limit f []))

  run el act cm 0     fbr st t = cedeFbr el fbr (run el act cm limit fbr st) t
  run el act 0  (S k) fbr st t =
    let s # t := read1 fbr.st t
     in case s.canceled of
          False => runR el act 0 k fbr st t
          True  => runC el act k fbr st t
  run el act c  (S k) fbr st t = runR el act c k fbr st t

  runC el act cc fbr st t =
    case act of
      UC f   => run el (f fbr.token 1) 1 cc fbr (Dec::st) t
      Term x => case st of
        Bnd f :: tl  => case f x of
          UC g => run el (g fbr.token 1) 1 cc fbr (Dec::tl) t
          a    => run el (pure ()) 1 cc fbr (hooks st) t
        Inc :: tl    => run el (Term x) 1 cc fbr tl t
        _           => run el (pure ()) 1 cc fbr (hooks st) t
      _    => run el (pure ()) 1 cc fbr (hooks st) t

  runR el act cm cc fbr st t =
    case act of
      Bind x f => case x of
        Term x => run el (f x) cm cc fbr st t
        _      => run el x cm cc fbr (Bnd f :: st) t

      Term x      => case st of
        Bnd f  :: tl => run el (f x) cm        cc fbr tl t
        Inc    :: tl => run el act   (S cm)    cc fbr tl t
        Dec    :: tl => run el act   (pred cm) cc fbr tl t
        -- ignore cancel hook because cancelation is currently not
        -- observable.
        Hook h :: tl => run el act   cm        cc fbr tl t
        Abort  :: tl => finalize fbr Canceled t
        []          => finalize fbr (toOutcome x) t

      Sync x      =>
        let r # t := ioToF1 x t
         in run el (Term r) cm cc fbr st t

      Cancel      => 
        let _ # t := doCancel fbr t
         in run el (pure ()) cm cc fbr st t

      OnCncl x y  => run el x cm cc fbr (Hook y :: st) t

      UC f        => run el (f fbr.token (S cm)) (S cm) cc fbr (Dec::st) t

      Env         =>
        let ev # t := read1 fbr.env t
         in run el (pure ev) cm cc fbr st t

      Cede        => cedeFbr el fbr (run el (pure ()) cm cc fbr st) t

      Start x     =>
        let fbr2 # t := newFiber el t
            _    # t := spawnFib el fbr2 x t
         in run el (pure $ toFiber fbr2) cm cc fbr st t

      Asnc f =>
        let res  # t := refIO Nothing t
            cncl # t := f (\r,t => let _ # t := put res r t in resume fbr t) t
         in run el (guaranteePrim (Wait res) cncl) cm cc fbr st t

      APoll tok k x => case tok == fbr.token && k == cm of
        True  => run el x (pred cm) cc fbr (Inc :: st) t
        False => run el x cm        cc fbr st t

      Wait res     =>
        case read1 res t of
          Just v  # t => run el (Term v) cm cc fbr st t
          Nothing # t => suspend fbr (el.spawn (Pkg fbr.env $ run el act cm limit fbr st)) t

  export covering
  runAsyncWith : EventLoop e -> Async e es a -> (Outcome es a -> IO ()) -> IO ()
  runAsyncWith el act cb = runIO $ \t =>
    let fbr # t := newFiber el t
        _   # t := observe fbr (\o => ioToF1 $ cb o) t
     in spawnFib el fbr act t
  
  export covering %inline
  runAsync : EventLoop e -> Async e es a -> IO ()
  runAsync el as = runAsyncWith el as (\_ => pure ())
