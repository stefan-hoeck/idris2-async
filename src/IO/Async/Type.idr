module IO.Async.Type

import Data.Nat
import IO.Async.Internal.ExecutionContext
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Timer
import IO.Async.Internal.Token
import System.Clock
import public IO.Async.Outcome

%default total

public export
0 Callback : List Type -> Type -> Type
Callback es a = Outcome es a -> PrimIO ()

public export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  cancel_  : PrimIO ()
  observe_ : Callback es a -> PrimIO (PrimIO ())

export
data Async : (es : List Type) -> Type -> Type where
  -- Implements bind (`>>=`) and error handling
  Bind   : Async es a -> (Result es a -> Async fs b) -> Async fs b

  -- A pure result (value or error)
  Term   : Result es a -> Async es a

  -- A wrapped synchronous/blocking IO action
  Sync   : IO (Result es a) -> Async es a

  -- Cancels the curret fiber
  Cancel : Async es ()

  -- Run the given cancel hook when cancelation is observed
  -- for `act`
  OnCncl : (act : Async es a) -> (hook : Async [] ()) -> Async es a

  -- Masks a fiber as uncanceble
  UC     : (Token -> Nat -> Async es a) -> Async es a

  -- Cedes control to the execution context
  Cede : Async es ()

  Start : Async es a -> Async fs (Fiber es a)

  Asnc   : ((Result es a -> PrimIO ()) -> PrimIO (PrimIO ())) -> Async es a

  -- Temporarily undo a layer of uncancelability
  APoll  : Token -> Nat -> Async es a -> Async es a

  -- Internal checking if asynchronous results are available.
  -- We only check after we have been notified that a result is ready.
  Wait : Ref (Maybe $ Result es a) -> Async es a

  WaitTill : Clock Monotonic -> Async es ()

--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

public export
0 Poll : Type
Poll = forall es,a . Async es a -> Async es a

||| Lifts a pure `Result` into `Async`.
export %inline
terminal : Result es a -> Async es a
terminal = Term

||| Lifts an effectful `Result` into `Async`.
export %inline
sync : IO (Result es a) -> Async es a
sync = Sync

||| Primitive for implementing `(>>=)` and error handling
export %inline
bind : Async es a -> (Result es a -> Async fs b) -> Async fs b
bind = Bind

||| Makes sure the given cancelation hook is run when `act` is canceled.
export %inline
onCancel : (act : Async es a) -> (hook : Async [] ()) -> Async es a
onCancel = OnCncl

||| Gracefully cancels execution of the current fiber.
export %inline
canceled : Async es ()
canceled = Cancel

||| Masks the given computation as *uncancelable* except for the regions
||| unmasked with the given `Poll`.
export %inline
uncancelable : (Poll -> Async es a) -> Async es a
uncancelable f = UC $ \t,n => f (APoll t n)

||| Semantically blocks the current fiber until the given time.
export %inline
waitTill : Clock Monotonic -> Async es ()
waitTill = WaitTill

||| Asynchronous FFI: Wraps a callback handler into `Async`.
|||
||| The `PrimIO ()` action returned after registering the callback will
||| be used for cancelation.
export %inline
primAsync : ((Result es a -> PrimIO ()) -> PrimIO (PrimIO ())) -> Async es a
primAsync = Asnc

||| Starts a new fiber, running it concurrently to the current one
export %inline
start : Async es a -> Async fs (Fiber es a)
start = Start

||| Cedes control back to the execution context.
export %inline
cede : Async es ()
cede = Cede

--------------------------------------------------------------------------------
-- Fiber Implementation (Here be Dragons)
--------------------------------------------------------------------------------

||| Lifts a value into `Async`.
export %inline
succeed : a -> Async es a
succeed = terminal . Right

||| Lifts an error `Result` into `Async`.
export %inline
fail : HSum es -> Async es a
fail = terminal . Left

export %inline
Functor (Async es) where
  map f x = bind x $ terminal . map f

export %inline
Applicative (Async es) where
  pure = succeed
  fa <*> ma = bind fa $ either fail (<$> ma)

export %inline
Monad (Async es) where
  x >>= f = bind x (either fail f)

export %inline
HasIO (Async es) where
  liftIO = sync . map Right

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
--                 it can be resumed by invoking the given `PrimIO` action.
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
  Suspended : PrimIO () -> FiberState es a
  HasResult : FiberState es a
  Done      : Outcome es a -> FiberState es a

-- Implementation of a `Fiber`
--
-- We use a `TokenGen` to identify observers, a `Token` to
-- identify the fiber during polls, a `Mutex` for synchronizing
-- state updates, and several mutable references representing the
-- fiber's current state.
record FiberST (es : List Type) (a : Type) where
  constructor FS
  ix       : Nat
  cbs      : List (Nat, Callback es a)
  canceled : Bool
  state    : FiberState es a

record FiberImpl (es : List Type) (a : Type) where
  constructor FI
  token  : Token
  submit : Ref ((k : PkgKind) -> PkgType k -> PrimIO ())
  st     : Ref (FiberST es a)

subDummy : (k : PkgKind) -> PkgType k -> PrimIO ()
subDummy = \_,_ => primDummy

-- allocates a new fiber, setting its initial state to `Running`
newFiber : TokenGen => PrimIO (FiberImpl es a)
newFiber w =
  let MkIORes t w := token w
      MkIORes r w := newRef subDummy w
      MkIORes s w := newRef (FS 0 [] False Running) w
   in MkIORes (FI t r s) w

-- remove the observer identified by the given token from the
-- list of callbacks.
stopObserving : Nat -> FiberImpl es a -> PrimIO ()
stopObserving n fbr = update fbr.st {cbs $= filter ((n /=) . fst)}

-- Registeres a callback at a fiber
-- If the fiber has already terminated (it is in its `Done` state),
-- the callback is immediately invoked and no cancel hook provided.
-- Otherwise, the callback is given a unique identifier and added to
-- the fiber's list of callbacks. A cancel hook for removing the
-- observer is returned in this case.
observe : FiberImpl es a -> Callback es a -> PrimIO (PrimIO ())
observe fbr cb w =
  let MkIORes ei w := modify fbr.st observeAct w
   in case ei of
        Left  act => let MkIORes _ w := act w in MkIORes primDummy w
        Right act => MkIORes act w
  where
    observeAct : FiberST es a -> (FiberST es a, (Either (PrimIO ()) (PrimIO ())))
    observeAct s =
      case s.state of
        Done o => (s, Left $ cb o)
        _      =>
         let s2 := {ix $= S, cbs $= ((s.ix,cb)::)} s
          in (s2, Right $ stopObserving s.ix fbr)

-- Cede control to the physical thread this fiber is running on
(.cede) : FiberImpl es a -> PrimIO () -> PrimIO ()
fbr.cede act w =
  let MkIORes f w := readRef fbr.submit w
   in f CPU act w

-- runs a list of callbacks
runCBs : List (Nat,Callback es a) -> Outcome es a -> PrimIO ()
runCBs []             o w = MkIORes () w
runCBs ((_,cb) :: xs) o w = let MkIORes _ w := cb o w in runCBs xs o w

-- Finalize the fiber with the given outcome and call all its observers.
finalize : FiberImpl es a -> Outcome es a -> PrimIO ()
finalize fbr o w = let MkIORes act w := modify fbr.st finAct w in act w

  where
    finAct : FiberST es a -> (FiberST es a, PrimIO ())
    finAct s = ({state := Done o, cbs := []} s, runCBs s.cbs o)

-- Cancel the given fiber, resuming its computation if it has
-- been suspended.
doCancel : FiberImpl es a -> PrimIO ()
doCancel fbr w = let MkIORes act w := modify fbr.st cancelAct w in act w

  where
    cancelAct : FiberST es a -> (FiberST es a, PrimIO ())
    cancelAct s =
      case s.state of
        Done _        => (s,primDummy)
        Suspended act => ({canceled := True, state := Running} s, act)
        _             => ({canceled := True} s, primDummy)

-- Suspend the fiber because it is waiting for the result of
-- an asynchronous computation. If the asynchronous computation
-- was faster, the fiber's state will be at `HasResult` and
-- it will immediately be resumed.
suspend : FiberImpl es a -> PrimIO () -> PrimIO ()
suspend fbr cont w = let MkIORes act w := modify fbr.st suspendAct w in act w

  where
    suspendAct : FiberST es a -> (FiberST es a, PrimIO ())
    suspendAct s =
      case s.state of
        HasResult => ({state := Running} s, cont) 
        _         => ({state := Suspended cont} s, primDummy) 

-- Resumes the computation of this fiber because the result from
-- an asynchronous computation is ready. If this is invoked while
-- the fiber is still running, we'll inform it that the result it
-- might be waiting for is ready, so that it will immediately
-- continue when it tries to suspend itself the next time.
--
-- If the fiber is already `Done`, well then we are much too late
-- and should abort silently.
resume : FiberImpl es a -> PrimIO ()
resume fbr w = let MkIORes act w := modify fbr.st resumeAct w in act w

  where
    resumeAct : FiberST es a -> (FiberST es a, PrimIO ())
    resumeAct s =
      case s.state of
        Suspended c => ({state := Running} s, c)
        Running     => ({state := HasResult} s, primDummy) 
        HasResult   => (s, primDummy)
        Done _      => (s, primDummy)

export
toFiber : FiberImpl es a -> Fiber es a
toFiber fbr = MkFiber (doCancel fbr) (observe fbr)

(.wait) :
     FiberImpl es a
  -> Clock Monotonic
  -> Ref Bool
  -> Ref (Maybe $ Result fs ())
  -> PrimIO ()
fbr.wait due cncl res w =
  let MkIORes f w := readRef fbr.submit w
   in f Timed (TT due cncl run) w

   where
     run : PrimIO ()
     run w =
       let MkIORes _ w := writeRef res (Just $ Right ()) w
        in resume fbr w

--------------------------------------------------------------------------------
-- Async Runner (More Dragons)
--------------------------------------------------------------------------------

data StackItem : (es,fs : List Type) -> (a,b : Type) -> Type where 
  Bnd   : (Result es a -> Async fs b) -> StackItem es fs a b
  Inc   : StackItem es es a a
  Abort : StackItem [] es () a
  Dec   : StackItem es es a a
  Hook  : Async [] () -> StackItem es es a a

-- Properly typed stack of nested `Bind`s plus instructions
-- related to cancelation and masking
data Stack : (es,fs : List Type) -> (a,b : Type) -> Type where
  Nil  : Stack es es a a
  (::) : StackItem es fs a b -> Stack fs gs b c -> Stack es gs a c

prepend : Async es a -> Stack es fs a b -> Stack [] fs () b
prepend act s = Bnd (const act) :: s

hooks : Stack es fs a b -> Stack [] fs () b
hooks (Hook h :: t) = prepend h (hooks t)
hooks (_ :: t)      = hooks t
hooks []            = [Abort]

parameters {auto ec : ExecutionContext}
           {auto tg : TokenGen}
           (limit   : Nat)

  -- Invokes runR or runC depending on if the fiber has
  -- been canceled and cancelation is currently observable
  covering
  run :
       Async es a
    -> (cancelMask  : Nat)
    -> (cedeCount   : Nat)
    -> FiberImpl fs b
    -> Stack es fs a b
    -> PrimIO ()

  covering
  runC :
       Async es a
    -> (cedeCount : Nat)
    -> FiberImpl fs b
    -> Stack es fs a b
    -> PrimIO ()

  covering
  runR :
       Async es a
    -> (cancelMask  : Nat)
    -> (cedeCount   : Nat)
    -> FiberImpl fs b
    -> Stack es fs a b
    -> PrimIO ()

  covering
  spawnFib : FiberImpl es a -> Async es a -> PrimIO ()
  spawnFib f act = ec.spawn (Pkg f.submit (run act 0 limit f []))

  run act cm 0     fbr st w = fbr.cede (run act cm limit fbr st) w
  run act 0  (S k) fbr st w =
    let MkIORes s w := readRef fbr.st w
     in case s.canceled of
          False => runR act 0 k fbr st w
          True  => runC act k fbr st w
  run act c  (S k) fbr st w = runR act c k fbr st w

  runC act cc fbr st w =
    case act of
      UC f   => run (f fbr.token 1) 1 cc fbr st w
      Term x => case st of
        Bnd f :: t  => case f x of
          UC g => run (g fbr.token 1) 1 cc fbr t w
          a    => run (pure ()) 1 cc fbr (hooks st) w
        Inc :: t    => run (Term x) 1 cc fbr t w
        _           => run (pure ()) 1 cc fbr (hooks st) w
      _    => run (pure ()) 1 cc fbr (hooks st) w

  runR act cm cc fbr st w =
    case act of
      Bind x f => case x of
        Term x => run (f x) cm cc fbr st w
        _      => run x cm cc fbr (Bnd f :: st) w

      Term x      => case st of
        Bnd f  :: t => run (f x) cm        cc fbr t w
        Inc    :: t => run act   (S cm)    cc fbr t w
        Dec    :: t => run act   (pred cm) cc fbr t w
        -- ignore cancel hook because cancelation is currently not
        -- observable.
        Hook h :: t => run act   cm        cc fbr t w
        Abort  :: t => finalize fbr Canceled w
        []          => finalize fbr (toOutcome x) w

      Sync x      =>
        let MkIORes r w := toPrim x w
         in run (Term r) cm cc fbr st w

      Cancel      => 
        let MkIORes _ w := doCancel fbr w
         in run (pure ()) cm cc fbr st w

      OnCncl x y  => run x cm cc fbr (Hook y :: st) w

      UC f        => run (f fbr.token (S cm)) (S cm) cc fbr (Dec::st) w

      Cede        => fbr.cede (run (pure ()) cm cc fbr st) w

      Start x     =>
        let MkIORes fbr2 w := newFiber w
            MkIORes _    w := spawnFib fbr2 x w
         in run (pure $ toFiber fbr2) cm cc fbr st w

      Asnc f =>
        let MkIORes res  w := newRef Nothing w
            MkIORes cncl w := f (\r,w => let MkIORes _ w := put res r w in resume fbr w) w
         in run (onCancel (Wait res) (primIO cncl)) cm cc fbr st w

      APoll t k x => case t == fbr.token && k == cm of
        True  => run x (pred cm) cc fbr (Inc :: st) w
        False => run x cm        cc fbr st w

      Wait res     =>
        let MkIORes mv w := readRef res w
         in case mv of
              Just v  => run (Term v) cm cc fbr st w
              Nothing =>
                let cont := ec.spawn (Pkg fbr.submit (run act cm limit fbr st))
                 in suspend fbr cont w

      WaitTill due =>
        let MkIORes res  w := newRef Nothing w
            MkIORes cncl w := newRef False w
            MkIORes _ w    := fbr.wait due cncl res w
            next := onCancel (Wait res) (primIO $ writeRef cncl True)
         in run next cm cc fbr st w

  export covering
  runAsyncWith : Async es a -> (Outcome es a -> IO ()) -> IO ()
  runAsyncWith act cb = fromPrim $ \w =>
    let MkIORes fbr w := newFiber w
        MkIORes _   w := observe fbr (\o => toPrim $ cb o) w
        MkIORes _   w := spawnFib fbr act w
     in ec.start w

  export covering %inline
  runAsync : Async es a -> IO ()
  runAsync as = runAsyncWith as (\_ => pure ())
