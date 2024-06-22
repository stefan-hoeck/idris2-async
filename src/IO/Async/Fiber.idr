module IO.Async.Fiber

import Data.IORef
import Data.Nat
import Data.SortedMap
import System.Concurrency
import IO.Async.Outcome
import IO.Async.Token

%default total

--------------------------------------------------------------------------------
-- Execution Context
--------------------------------------------------------------------------------

||| A context for submitting and running commands asynchronously.
public export
record ExecutionContext where
  [noHints]
  constructor EC
  tokenGen : TokenGen
  submit   : IO () -> IO ()
  limit    : Nat

export %inline %hint
ecToTokenGen : ExecutionContext => TokenGen
ecToTokenGen @{ec} = ec.tokenGen

--------------------------------------------------------------------------------
-- Fiber
--------------------------------------------------------------------------------

||| A fiber is a synchronous (sequential) computation producing
||| an outcome of type `Outcome es a` eventually.
|||
||| We can register a callback at a fiber to get informed about its
||| termination, and we can externally interrupt a running fiber
||| by canceling it.
public export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  token         : Token
  observe       : Token -> (Outcome es a -> IO ()) -> IO ()
  stopObserving : Token -> IO ()
  cancel        : IO ()

--------------------------------------------------------------------------------
-- Async
--------------------------------------------------------------------------------

||| `Async es a` is a monad for describing asynchronous computations
||| producing a result of type `Outcome es a` eventually.
export
data Async : (es : List Type) -> Type -> Type

||| Different ways to inform an asynchronous computation
||| that the fiber waiting for the computation to finish has
||| been canceled.
public export
data AsyncHandler : Type where
  ||| No way to cancel this computation. We must wait this out.
  Wait   : AsyncHandler

  ||| The computation can't be canceled.
  |||
  ||| If the fiber waiting for it has been canceled and is not in
  ||| an `uncancelable` block, it will ignore the computation and
  ||| just move on. If the fiber is uncancelable, it will wait for
  ||| the computation to finish.
  Proceed : AsyncHandler

  ||| The computation can be canceled and should be notified
  ||| when the fiber waiting for it has been canceled. Afterwards,
  ||| the fiber will semantically block until the computation produces
  ||| a result.
  |||
  ||| Note: The cancel hook will be invoked even if the fiber is
  |||       currently uncancelable.
  Notify : Async [] () -> AsyncHandler

  ||| The computation can be canceled and should be notified
  ||| when the fiber waiting for it has been canceled and is not
  ||| currently uncancelable. Afterwards
  ||| the fiber will semantically block until the computation produces
  ||| a result.
  NotifyIfCancelable : Async [] () -> AsyncHandler
  

data Async : (es : List Type) -> Type -> Type where
  -- Primitives

  -- Implements bind (`>>=`) and error handling
  Bind   : Async es a -> (Result es a -> Async fs b) -> Async fs b

  -- A pure result (value or error)
  Term   : Result es a -> Async es a

  -- A wrapped synchronous IO action
  Sync   : IO (Result es a) -> Async es a

  -- Spawns a new child fiber
  Start  : Async es a -> Async fs (Fiber es a)

  -- Cancels the curret fiber
  Cancel : Async es ()

  -- Run the given cancel hook when cancelation is observed
  -- for this fiber
  OnCncl : Async es a -> Async [] () -> Async es a

  -- Shiftes execution to a different context
  Shift  : ExecutionContext -> Async es ()

  -- Returns the ID token of the current fiber
  Self   : Async es Token

  -- Cede control to another fiber by resubmitting the current
  -- computation to the execution context.
  Cede   : Async es ()

  -- A wrapped asynchronous computation with potential cancel
  -- function.
  Asnc   : ((Result es a -> IO ()) -> IO AsyncHandler) -> Async es a

  -- Returns the execution context the fiber is currently running on
  GetEC  : Async es ExecutionContext

  -- Masks this fiber as uncancable
  UC     : (Nat -> Async es a) -> Async es a

  -- Temporarily undo a layer of uncancelability
  APoll  : Nat -> Async es a -> Async es a

  -- Waits till the given `MVar` holds a result unless
  -- the `AsyncHandler` is set to `Proceed` and the fiber has been
  -- canceled.
  Await  : IORef (Maybe $ Result es a) -> Token -> AsyncHandler -> Async es a

public export
0 Poll : Type
Poll = {0 es : _} -> {0 a : _} -> Async es a -> Async es a

--------------------------------------------------------------------------------
-- Interface Implementations
--------------------------------------------------------------------------------

export %inline
succeed : a -> Async es a
succeed = Term . Right

export %inline
sync : IO (Result es a) -> Async es a
sync = Sync

bind : Async es a -> (a -> Async es b) -> Async es b
bind x f =
  Bind x $ \case
    Right v => f v
    Left x  => Term (Left x)

export
Functor (Async es) where
  map f aa = bind aa (succeed . f)

export %inline
Applicative (Async es) where
  pure      = succeed
  af <*> aa = bind af (<$> aa)

export %inline
Monad (Async es) where
  (>>=) = bind

export
HasIO (Async es) where
  liftIO = sync . map Right

--------------------------------------------------------------------------------
-- Asynchronicity
--------------------------------------------------------------------------------

||| Returns the unique token of the currently running fiber.
export %inline
self : Async es Token
self = Self

||| Runs an asynchronous computation that returns a cancel hook after
||| registering the callback.
|||
||| The cancel hook will only be invoked if cancelation can currently be
||| observed, that is, we are currently not in an uncancelable block.
export %inline
cancelableAsync : ((Result es a -> IO ()) -> IO (Async [] ())) -> Async es a
cancelableAsync f = Asnc (map NotifyIfCancelable . f)

||| Runs an asynchronous computation.
|||
||| In case of the current fiber being canceled, this will not wait
||| for a result from the callback and will just move on.
export %inline
async : ((Result es a -> IO ()) -> IO ()) -> Async es a
async f = Asnc (\o => f o $> Proceed)

||| Runs an asynchronous computation.
|||
||| In case of the current fiber being canceled, this will wait for
||| the computation to finish no matter what.
export %inline
blockingAsync : ((Result es a -> IO ()) -> IO ()) -> Async es a
blockingAsync f = Asnc (\o => f o $> Wait)

export
lazy : Lazy a -> Async es a
lazy v = async (\f => f $ Right v)

||| Cede control to a different fiber by resubmitting the current
||| computation to the execution context.
export %inline
cede : Async es ()
cede = Cede

--------------------------------------------------------------------------------
-- Cancelation
--------------------------------------------------------------------------------

||| The asynchronous operation that never produces a result.
|||
||| This can be canceled but not when it is in an uncancelable
||| block, in which case it will never ever terminate.
export %inline
never : Async es a
never = async (\_ => pure ())

||| Masks the given asynchronous computation as "uncancelable".
|||
||| You can use the `Poll` argument to still mark certain regions
||| to be cancelable.
export %inline
uncancelable : (Poll -> Async es a) -> Async es a
uncancelable f = UC $ \n => f $ APoll n

||| Cancels the current fiber as soon as possible.
|||
||| Note: This will *always* result in fiber cancelation unless the fiber already
|||       terminated with a different result. Even when in an uncancable section,
|||       this will mark the fiber as being canceled and cancelation will be
|||       observed as soon as possible. There us no way to undo cancelation of
|||       a fiber.
export %inline
canceled : Async es ()
canceled = Cancel

||| This is an alias for `canceled >> never`.
|||
||| The advantage of this is that unlike `canceled` it claims to produce
||| a value of any type. This is useful when using it to join fibers in
||| cancelable environment. However, if this is used in an uncancelable
||| section, it will unvariably deadlock forever.
export %inline
cancelOrDeadlock : Async es a
cancelOrDeadlock = canceled >> never

--------------------------------------------------------------------------------
-- MonadError
--------------------------------------------------------------------------------

export %inline
fail : HSum es -> Async es a
fail = Term . Left

export %inline
throw : Has e es => e -> Async es a
throw = fail . inject

||| Inject an `Either e a` computation into an `Async` monad dealing
||| with several possible errors.
export
injectEither : Has e es => Either e a -> Async es a
injectEither (Left v)  = throw v
injectEither (Right v) = pure v

||| Inject an `IO (Either e a)` computation into an `Async` monad dealing
||| with several possible errors.
export
injectIO : Has e es => IO (Either e a) -> Async es a
injectIO = sync . map (mapFst inject)

export
handleErrors : (HSum es -> Async fs a) -> Async es a -> Async fs a
handleErrors f x = Bind x $ either f pure

export %inline
mapErrors : (HSum es -> HSum fs) -> Async es a -> Async fs a
mapErrors f = handleErrors (fail . f)

export %inline
weakenErrors : Async [] a -> Async fs a
weakenErrors = mapErrors $ \case x impossible

export %inline
dropErrs : Async es () -> Async [] ()
dropErrs = handleErrors (const $ pure ())

public export
0 Handler : Type -> Type -> Type
Handler a x = x -> Async [] a

export %inline
handle : All (Handler a) es -> Async es a -> Async [] a
handle hs = handleErrors (collapse' . hzipWith id hs)

export %inline
liftErrors : Async es a -> Async fs (Result es a)
liftErrors = handleErrors (pure . Left) . map Right

export %inline
liftError : Async [e] a -> Async fs (Either e a)
liftError = handleErrors (pure . Left . project1) . map Right

export %inline
onCancel : Async es a -> Async [] () -> Async es a
onCancel = OnCncl

export
guaranteeCase : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
guaranteeCase as f =
  uncancelable $ \poll =>
    let finalized := onCancel(poll as)(f Canceled)
     in Bind finalized $ \case
          Left errs => Bind (f $ Error errs) (\_ => fail errs)
          Right v   => Bind (f $ Succeeded v) (\_ => pure v)

||| Guarantees to run the given cleanup hook in case a fiber
||| has been canceled or failed with an error.
|||
||| See `guarantee` for additional information.
export
onAbort : Async es a -> (cleanup : Async [] ()) -> Async es a
onAbort as h =
  guaranteeCase as $ \case
    Canceled => h
    Error _  => h
    _        => pure ()

||| Guarantees to run the given cleanup hook in case
||| the given computation finishes with an outcome.
|||
||| See `guarantee` for additional information.
export %inline
finally : Async es a -> (cleanup : Async [] ()) -> Async es a
finally aa v = guaranteeCase aa (\_ => v)

export %inline
forget : Async es a -> Async [] ()
forget as = Bind as (\_ => pure ())

export
consume : Async es a -> (Outcome es a -> IO ()) -> Async [] ()
consume as cb = forget $ guaranteeCase as (liftIO . cb)

export
bracketFull :
     (acquire : Poll -> Async es a)
  -> (use     : a -> Async es b)
  -> (release : a -> Outcome es b -> Async [] ())
  -> Async es b
bracketFull acquire use release =
  uncancelable $ \poll => do
    v <- acquire poll
    guaranteeCase (poll $ use v) (release v)

export %inline
bracketCase :
     Async es a
  -> (a -> Async es b)
  -> (a -> Outcome es b -> Async [] ())
  -> Async es b
bracketCase acquire use release = bracketFull (\_ => acquire) use release

export %inline
bracket : Async es a -> (a -> Async es b) -> (a -> Async [] ()) -> Async es b
bracket acquire use release = bracketCase acquire use (const . release)

--------------------------------------------------------------------------------
-- Working with Fibers
--------------------------------------------------------------------------------

||| Runs an asynchronous computation in the background on a new fiber.
|||
||| The resulting fiber can be canceled from the current fiber, and
||| we can semantically block the current fiber to wait for the background
||| computation to complete.
|||
||| See also `cancel` and `join`.
export %inline
start : Async es a -> Async fs (Fiber es a)
start as = Start as

export
join : Fiber es a -> Async fs (Outcome es a)
join f = do
  t <- self
  cancelableAsync $ \cb =>
    f.observe t (cb . Right) $>
    liftIO (f.stopObserving t >> cb (Right Canceled))

export
joinMaybe : Fiber es a -> Async es (Maybe a)
joinMaybe f =
  join f >>= \case
    Succeeded v => pure (Just v)
    Canceled    => pure Nothing
    Error errs  => fail errs

export
joinWith : (onCancel : Async es a) -> Fiber es a -> Async es a
joinWith onCancel f =
  join f >>= \case
    Succeeded x => pure x
    Error err   => Term $ Left err
    Canceled    => onCancel

||| Waits for the given fiber to finish and continues with
||| its result: If it fails with an error, the current fiber will
||| also throw an error, if it is canceled, so is the current
||| fiber.
|||
||| This will deadlock if the target fiber is canceled and we are
||| in an uncancelable section.
export
joinOrDeadlock : Fiber es a -> Async es a
joinOrDeadlock = joinWith cancelOrDeadlock

||| Cancels the given fiber and awaits its termination
||| be semantically blocking the calling fiber.
export
cancel : Fiber es a -> Async fs ()
cancel f =
  uncancelable $ \poll => do
    liftIO $ f.cancel
    poll (ignore (join f))

||| Asynchronously runs a computation on a new fiber.
|||
||| While we can no longer observe the computation's result, it will still
||| be canceled if the current fiber terminates.
export %inline
background : Async es a -> Async fs ()
background = ignore . start

--------------------------------------------------------------------------------
-- Concurrency
--------------------------------------------------------------------------------

||| Semantically blocks the current fiber until one
||| of the given fibers has produced an outcome, in which
||| case the others are canceled immediately.
|||
||| This is useful if you for instance have several abort conditions
||| such as a timer and a signal from the operating system, and want
||| to stop your process as soon as the first of the conditions
||| occurs.
export
raceF : List (Async es (Fiber es a)) -> Async es (Maybe a)
raceF fs = do
  t    <- self
  fibs <- sequence fs
  finally
    (async (\cb => for_ fibs (\f => f.observe t (cb . fromOutcome))))
    (stop t fibs)

  where
    stop : Token -> List (Fiber es a) -> Async [] ()
    stop t fs = liftIO $ for_ fs $ \f => f.stopObserving t >> f.cancel

||| Alias for `raceF . traverse start`.
export %inline
race : (xs : List $ Async es a) -> Async es (Maybe a)
race = raceF . map start

injections : All f ts -> All (\t => (v : t) -> HSum ts) ts
injections []        = []
injections (x :: xs) = Here :: mapProperty (There .) (injections xs)

||| Runs a heterogeneous list of asynchronous computations in parallel,
||| keeping only the one that finishes first.
export %inline
raceAny : All (Async es) ts -> Async es (Maybe $ HSum ts)
raceAny xs = race . forget $ hzipWith map (injections xs) xs

||| Accumulates the results of the given heterogeneous list of
||| fibers in a heterogeneous list.
|||
||| This returns `Nothing` if one of the fibers was canceled.
export
parF : All (Async es . Fiber es) ts -> Async es (Maybe $ HList ts)
parF fs = do
  fibers <- hsequence fs
  hsequence <$> hsequence (mapProperty joinMaybe fibers)

||| Like `parF` but cancels the current fiber if one of the
||| child computations is canceled.
|||
||| This uses `cancelOrDeadlock` internally, so it comes with
||| the risk of deadlocking.
export
unsafeParF : All (Async es . Fiber es) ts -> Async es (HList ts)
unsafeParF fs = do
  fibers <- hsequence fs
  hsequence (mapProperty joinOrDeadlock fibers)

||| Runs the given computations in parallel and collects the outcomes
||| in a heterogeneous list.
|||
||| This returns `Nothing` if one of the fibers was canceled.
export %inline
par : All (Async es) ts -> Async es (Maybe $ HList ts)
par = parF . mapProperty start

||| Like `par` but cancels the current fiber if one of the
||| child computations is canceled.
|||
||| This uses `cancelOrDeadlock` internally, so it comes with
||| the risk of deadlocking.
export %inline
unsafePar : All (Async es) ts -> Async es (HList ts)
unsafePar = unsafeParF . mapProperty start

||| Traverses a list of values effectfully in parallel.
|||
||| This returns `Nothing` if one of the fibers was canceled.
export
parTraverse : (a -> Async es b) -> List a -> Async es (Maybe $ List b)
parTraverse f vs = do
  fibers <- traverse (start . f) vs
  sequence <$> traverse joinMaybe fibers

export covering
runAsyncWith : ExecutionContext => Async es a -> (Outcome es a -> IO ()) -> IO ()

export covering %inline
runAsync : ExecutionContext => Async es a -> IO ()
runAsync as = runAsyncWith as (\_ => pure ())

--------------------------------------------------------------------------------
-- Implementation (Here be Dragons)
--------------------------------------------------------------------------------

data StackItem : (es,fs : List Type) -> (a,b : Type) -> Type where 
  Cont     : (Result es a -> Async fs b) -> StackItem es fs a b
  IncUC    : StackItem es es a a
  Abort    : StackItem [] es () a
  DecUC    : StackItem es es a a
  CnclHook : Async [] () -> StackItem es es a a

-- Properly typed stack of nested `Bind`s plus their cancelability
data Stack : (es,fs : List Type) -> (a,b : Type) -> Type where
  Nil  : Stack es es a a
  (::) : StackItem es fs a b -> Stack fs gs b c -> Stack es gs a c

-- Current stat of a fiber
data FiberState : List Type -> Type -> Type where
  -- The fiber has just been initialized with the asynchronous
  -- computation it is about to run.
  Init        : Async es a -> FiberState es a

  -- The fiber is currently being run on its execution context
  Running     : FiberState es a

  -- The fiber produced an outcome and ist now finished.
  Done        : Outcome es a -> FiberState es a

  -- The fiber is awaiting the result from an asynchronous
  -- computation, and is currently not being run.
  Suspended   :
       IORef (Maybe $ Result es a)
    -> Token
    -> (cnclAsync  : AsyncHandler)
    -> (cancelMask : Nat)
    -> Stack es fs a b
    -> FiberState fs b

prepend : Async es a -> Stack es fs a b -> Stack [] fs () b
prepend act s = Cont (const act) :: s

record FiberImpl (es : List Type) (a : Type) where
  constructor FI
  ec        : IORef ExecutionContext
  mutex     : Mutex
  token     : Token
  callbacks : IORef (SortedMap Token (Outcome es a -> IO ()))
  canceled  : IORef Bool
  state     : IORef (FiberState es a)

withLock : FiberImpl es a -> IO b -> IO b
withLock fbr f = do
  mutexAcquire fbr.mutex
  res <- f
  mutexRelease fbr.mutex
  pure res

newFiber : ExecutionContext -> (as : Async es a) -> IO (FiberImpl es a)
newFiber ec as =
  [| FI
       (newIORef ec)
       makeMutex
       token
       (newIORef empty)
       (newIORef False)
       (newIORef $ Init as)
  |]

stopObservingImpl : FiberImpl es a -> Token -> IO ()
stopObservingImpl fbr tk = withLock fbr $ modifyIORef fbr.callbacks (delete tk)

observeImpl : FiberImpl es a -> Token -> (Outcome es a -> IO ()) -> IO ()
observeImpl fbr tk cb = do
  run <- withLock fbr $
    readIORef fbr.state >>= \case
      Done o => pure (cb o)
      _      => modifyIORef fbr.callbacks (insert tk cb) $> pure ()
  run

covering
run :
     {auto ec : ExecutionContext}
  -> Nat
  -> FiberImpl fs b
  -> Async es a
  -> (cancelMask  : Nat)
  -> Stack es fs a b
  -> IO ()

-- This function is invoked if
--   a) The fiber was canceled
--   b) The result of a callback is ready
covering
resume : FiberImpl es a -> Maybe Token -> IO ()
resume fbr mtok = do
  -- This might be invoked from several threads, so we
  -- adjust the state and assemble the action to run under
  -- a lock. The action is run after the mutex was released.
  run <- withLock fbr $ do
    readIORef fbr.state >>= \case
      Suspended ref tok cncl m s => case maybe True (tok ==) mtok of
        True => do
          writeIORef fbr.state Running
          ec <- readIORef fbr.ec
          pure (run @{ec} ec.limit fbr (Await ref tok cncl) m s)
        False => pure (pure ())

      -- Hello world! This is a new fiber, so let's run it!
      Init as => do
        writeIORef fbr.state Running
        ec <- readIORef fbr.ec
        pure (run @{ec} ec.limit fbr as 0 [])

      -- we are already running or done, so don't interfere
      _  => pure (pure ())
  run -- actually run the action we got

covering
cancelImpl : FiberImpl es a -> IO ()
cancelImpl fbr = do
  run <- withLock fbr $ do -- make sure no one else adjusts the state
    readIORef fbr.canceled >>= \case
      True  => pure (pure ()) -- we have already been canceled, so that's being take care of
      False => writeIORef fbr.canceled True $> resume fbr Nothing
  run

suspend   :
     FiberImpl fs b
  -> IORef (Maybe $ Result es a)
  -> Token
  -> (cnclAsync  : AsyncHandler)
  -> (cancelMask : Nat)
  -> Stack es fs a b
  -> IO (IO ())
suspend fbr ref tok cncl m s =
  writeIORef fbr.state (Suspended ref tok cncl m s) $> pure ()

-- We have a result and the fiber can be finalized.
-- This can only be called from a running fiber, so we don't have
-- to check the state here.
covering
finalize : FiberImpl es a -> Outcome es a -> IO ()
finalize fbr o = do
  run <- withLock fbr $ do -- make sure no one else adjusts the state
    -- We won the race, so we set the state to "Done" before anybody else does.
    writeIORef fbr.state (Done o)

    -- Read and empty the callbacks...
    cbs <- readIORef fbr.callbacks
    writeIORef fbr.callbacks empty

    -- ...and invoke all callbacks and cancel all children
    pure $ for_ cbs (\cb => cb o)

  run -- actually run the action we got

covering (.fiber) : FiberImpl es a -> Fiber es a
f.fiber = MkFiber f.token (observeImpl f) (stopObservingImpl f) (cancelImpl f)

hooks : Stack es fs a b -> Stack [] fs () b
hooks (CnclHook h :: t) = prepend h (hooks t)
hooks (_ :: t)          = hooks t
hooks []                = [Abort]

covering
doCancel :
     {auto ec : ExecutionContext}
  -> Nat
  -> FiberImpl fs b
  -> Async es a
  -> Stack es fs a b
  -> IO ()
doCancel n f (Await r t c) s =
  case c of
    Wait                 => run n f (forget $ Await r t Wait) 1 (hooks s)
    Proceed              => run n f (pure ()) 1 (hooks s)
    Notify x             => run n f (x >> forget (Await r t Wait)) 1 (hooks s)
    NotifyIfCancelable x => run n f (x >> forget (Await r t Wait)) 1 (hooks s)
doCancel n f _ s = run n f (pure ()) 1 (hooks s)

run n fbr act m stck = do
  cncld <- withLock fbr (readIORef fbr.canceled)
  False <- pure (cncld && m == 0) | True => doCancel n fbr act stck
  S k   <- pure n | 0 => ec.submit (run ec.limit fbr act m stck)
  case act of
    Bind x f => run k fbr x m (Cont f :: stck)

    Term o => case stck of
      Cont f     :: fs => run k fbr (f o) m fs
      IncUC      :: fs => run k fbr act (S m) fs
      DecUC      :: fs => run k fbr act (pred m) fs
      -- ignore cancel hook because cancelation is currently not
      -- observable.
      CnclHook h :: fs => run k fbr act m fs
      Abort      :: fs => finalize fbr Canceled
      []               => finalize fbr (toOutcome o)

    Sync io => do
      r <- io
      run k fbr (Term r) m stck

    Start as => do
      child <- newFiber ec as
      ec.submit (resume child Nothing)
      run k fbr (pure child.fiber) m stck
    
    Shift ec2 => do
      writeIORef fbr.ec ec2 >>
      ec2.submit (run @{ec2} k fbr (pure ()) m stck)

    Cede => ec.submit (run ec.limit fbr (pure ()) m stck)

    Self => run k fbr (pure fbr.token) m stck

    Cancel => do
      withLock fbr (writeIORef fbr.canceled True) >>
      run k fbr (pure ()) m stck

    UC f => run k fbr (f (S m)) (S m) (DecUC :: stck)

    APoll j x => case j == m of
      True  => run k fbr x (pred m) (IncUC :: stck)
      False => run k fbr x m stck

    GetEC => run k fbr (pure ec) m stck

    OnCncl x c => run k fbr x m (CnclHook c :: stck)

    Asnc reg => do
      tok <- token
      ref <- newIORef Nothing
      cnl <- reg $ \o => do
        act <- withLock fbr $ do
          Nothing <- readIORef ref | _ => pure (pure ())
          writeIORef ref (Just o)
          pure (resume fbr $ Just tok)
        act
      run k fbr (Await ref tok cnl) m stck

    Await ref tok c => do
      act <- withLock fbr $ do
        Nothing <- readIORef ref | Just r => pure (run k fbr (Term r) m stck)
        case cncld of
          False => suspend fbr ref tok c m stck
          True  => case c of
            Wait    => suspend fbr ref tok Wait m stck
            Proceed => suspend fbr ref tok Wait m stck
            Notify h =>
              pure (run k fbr h m $ prepend (Await ref tok Wait) stck)
            NotifyIfCancelable _ => suspend fbr ref tok Wait m stck
      act

runAsyncWith @{ec} as cb = do
  fib <- newFiber ec as
  tk  <- token
  observeImpl fib tk cb
  ec.submit (resume fib Nothing)
