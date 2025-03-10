module IO.Async.Type

import Debug.Trace
import Data.Nat
import IO.Async.Loop
import IO.Async.Internal.Ref
import Data.Linear.Deferred
import Data.Linear.Unique

import public Control.Monad.MCancel
import public Data.Linear.ELift1

%default total

public export
0 Callback : List Type -> Type -> Type
Callback es a = Outcome es a -> IO1 ()

public export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  cancel_  : IO1 ()
  observe_ : Callback es a -> IO1 (IO1 ())

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
  UC     : (Token World -> Nat -> Async e es a) -> Async e es a

  Attempt : Async e es a -> Async e fs (Result es a)

  -- Returns the context currently handling this fiber, giving us access
  -- to functionality specific to the running event loop.
  Env  : Async e es e

  -- Cedes control to the execution context
  Cede : Async e es ()

  Start : Async e es a -> Async e fs (Fiber es a)

  Asnc   : ((Result es a -> IO1 ()) -> IO1 (IO1 ())) -> Async e es a

  -- Temporarily undo a layer of uncancelability
  APoll  : Token World -> Nat -> Async e es a -> Async e es a

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

--------------------------------------------------------------------------------
-- Fiber Implementation (Here be Dragons)
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

--------------------------------------------------------------------------------
-- Fiber Implementation (Here be Dragons)
--------------------------------------------------------------------------------

record FiberImpl (e : Type) (es : List Type) (a : Type) where
  constructor FI
  ||| Unique identifier of the fiber
  token  : Token World

  ||| Environment provided by the run loop
  env    : IORef e

  ||| Set, if the fiber has been canceled.
  cncl   : Once World ()

  ||| Set, if the fiber has run to completion.
  res    : Deferred World (Outcome es a)

-- allocates a new fiber, setting its initial state to `Running`
newFiber : EventLoop e -> IO1 (FiberImpl e es a)
newFiber el t =
  let tok  # t := Unique.token1 t
      env  # t := ref1 el.init t
      cncl # t := onceOf1 () t
      res  # t := deferredOf1 (Outcome es a) t
   in FI tok env cncl res # t

-- Cede control to the physical thread this fiber is running on
cedeFbr : EventLoop e -> FiberImpl e es a -> IO1 () -> IO1 ()
cedeFbr el fbr act = el.cede (Pkg fbr.env act)

-- Finalize the fiber with the given outcome and call all its observers.
%inline
finalize : FiberImpl e es a -> Outcome es a -> IO1 ()
finalize fbr o = putDeferred1 fbr.res o

toFiber : FiberImpl e es a -> Fiber es a
toFiber fbr = MkFiber (putOnce1 fbr.cncl ()) (observeDeferred1 fbr.res)

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

parameters (limit   : Nat)

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
    case completedOnce1 fbr.cncl t of
      False # t => runR el act 0 k fbr st t
      True  # t => runC el act k fbr st t
  run el act c  (S k) fbr st t = runR el act c k fbr st t

  runC el act cc fbr st t =
    case act of
      UC f   => run el (f fbr.token 1) 1 cc fbr (Dec::st) t
      Val x => case st of
        Bnd f :: tl  => case f (Right x) of
          UC g => run el (g fbr.token 1) 1 cc fbr (Dec::tl) t
          a    => run el (pure ()) 1 cc fbr (hooks st) t
        Inc :: tl    => run el (Val x) 1 cc fbr tl t
        _           => run el (pure ()) 1 cc fbr (hooks st) t
      Err x => case st of
        Bnd f :: tl  => case f (Left x) of
          UC g => run el (g fbr.token 1) 1 cc fbr (Dec::tl) t
          a    => run el (pure ()) 1 cc fbr (hooks st) t
        Inc :: tl    => run el (Err x) 1 cc fbr tl t
        _           => run el (pure ()) 1 cc fbr (hooks st) t
      _    => run el (pure ()) 1 cc fbr (hooks st) t

  runR el act cm cc fbr st t =
    case act of
      Bind x f => case x of
        Val x => run el (f x) cm cc fbr st t
        _     => run el x cm cc fbr (Bnd (either Err f) :: st) t

      Val x      => case st of
        Bnd f  :: tl => run el (f $ Right x) cm        cc fbr tl t
        Inc    :: tl => run el act   (S cm)    cc fbr tl t
        Dec    :: tl => run el act   (pred cm) cc fbr tl t
        -- ignore cancel hook because cancelation is currently not
        -- observable.
        Hook h :: tl => run el act   cm        cc fbr tl t
        Abort  :: tl => finalize fbr Canceled t
        []          => finalize fbr (Succeeded x) t

      Err x      => case st of
        Bnd f  :: tl => run el (f $ Left x) cm        cc fbr tl t
        Inc    :: tl => run el act   (S cm)    cc fbr tl t
        Dec    :: tl => run el act   (pred cm) cc fbr tl t
        -- ignore cancel hook because cancelation is currently not
        -- observable.
        Hook h :: tl => run el act   cm        cc fbr tl t
        Abort  :: tl => finalize fbr Canceled t
        []          => finalize fbr (Error x) t

      Start x     =>
        let fbr2 # t := newFiber el t
            _    # t := spawnFib el fbr2 x t
         in run el (pure $ toFiber fbr2) cm cc fbr st t

      Sync x      =>
        let r # t := ioToF1 x t
         in run el (terminal r) cm cc fbr st t

      Attempt x => run el x cm cc fbr (Bnd Val :: st) t

      Cancel      => 
        let _ # t := putOnce1 fbr.cncl () t
         in run el (pure ()) cm cc fbr st t

      OnCncl x y  => run el x cm cc fbr (Hook y :: st) t

      UC f        => run el (f fbr.token (S cm)) (S cm) cc fbr (Dec::st) t

      Env         =>
        let ev # t := read1 fbr.env t
         in run el (pure ev) cm cc fbr st t

      Cede        => cedeFbr el fbr (run el (pure ()) cm cc fbr st) t

      Asnc f => case cm of
        -- Cancelation is currently observable, so we listen for
        -- cancelation as well as the completion of the async computation.
        -- Both results are raced and written to a `Once`, on which we listen
        -- to be notified about the continuation.
        0 =>
          let o  # t := onceOf1 (Outcome es a) t
              c1 # t := f (putOnce1 o . toOutcome) t
              c2 # t := observeOnce1 fbr.cncl (\_ => putOnce1 o Canceled) t
              _  # t := observeOnce1 o (\out,t => case out of
                          Succeeded r => let _ # t := c2 t in el.spawn (Pkg fbr.env $ run el (Val r) cm cc fbr st) t
                          Error     x => let _ # t := c2 t in el.spawn (Pkg fbr.env $ run el (Err x) cm cc fbr st) t
                          Canceled    => let _ # t := c1 t in el.spawn (Pkg fbr.env $ run el (pure ()) 1 cc fbr (hooks st)) t
                        )t
           in () # t

        -- Cancelation is currently not observable, so we ignore the cancel
        -- hook and just register the callback.
        _ =>
          let cncl # t := f (\r => run el (terminal r) cm cc fbr st) t
           in trace "Warning: Cant cancel async operation (\{show cm})" () # t

      APoll tok k x => case tok == fbr.token && k == cm of
        True  => run el x (pred cm) cc fbr (Inc :: st) t
        False => run el x cm        cc fbr st t

  export covering
  runAsyncWith : EventLoop e -> Async e es a -> (Outcome es a -> IO ()) -> IO ()
  runAsyncWith el act cb = runIO $ \t =>
    let fbr # t := newFiber el t
        _   # t := observeDeferred1 fbr.res (\o => ioToF1 $ cb o) t
     in spawnFib el fbr act t
  
  export covering %inline
  runAsync : EventLoop e -> Async e es a -> IO ()
  runAsync el as = runAsyncWith el as (\_ => pure ())
