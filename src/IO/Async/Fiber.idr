module IO.Async.Fiber

import Data.IORef
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
data Async : (es : List Type) -> Type -> Type where
  Term   : Outcome es a -> Async es a

  Sync   : IO (Result es a) -> Async es a

  Start  : Async es a -> Async fs (Fiber es a)

  Shift  : ExecutionContext -> Async es ()

  Self   : Async es Token

  Cancel : Async es ()

  GetEC  : Async es ExecutionContext

  Asnc   : ((Outcome es a -> IO ()) -> IO (Maybe $ Async [] ())) -> Async es a

  Bind   : Async es a -> (Outcome es a -> Async fs b) -> Async fs b

  UC     : (Nat -> Async es a) -> Async es a

  ContUC : Nat -> Async es ()

  APoll  : Nat -> Async es a -> Async es a

  StopUC : Async es ()

public export
0 Poll : Type
Poll = {0 es : _} -> {0 a : _} -> Async es a -> Async es a

--------------------------------------------------------------------------------
-- Interface Implementations
--------------------------------------------------------------------------------

export %inline
succeed : a -> Async es a
succeed = Term . Succeeded

export %inline
sync : IO (Result es a) -> Async es a
sync = Sync

bind : Async es a -> (a -> Async es b) -> Async es b
bind x f =
  Bind x $ \case
    Succeeded v => f v
    Error x     => Term (Error x)
    Canceled    => Term Canceled

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
-- Cancelation
--------------------------------------------------------------------------------

export %inline
uncancelable : (Poll -> Async es a) -> Async es a
uncancelable f = UC $ \n => f $ APoll n

export
canceled : Async es ()
canceled = Cancel

--------------------------------------------------------------------------------
-- Asynchronicity
--------------------------------------------------------------------------------

||| Returns the unique token of the currently running fiber.
export %inline
self : Async es Token
self = Self

export %inline
cancelableAsync : ((Outcome es a -> IO ()) -> IO (Async [] ())) -> Async es a
cancelableAsync f = Asnc (map Just . f)

export %inline
async : ((Outcome es a -> IO ()) -> IO ()) -> Async es a
async f = Asnc (\o => f o $> Nothing)

export
lazy : Lazy a -> Async es a
lazy v = async (\f => f $ Succeeded v)

export
join : Fiber es a -> Async fs (Outcome es a)
join f = do
  t <- self
  cancelableAsync $ \cb =>
    f.observe t (cb . Succeeded) $> liftIO (f.stopObserving t)

export
joinResult : Fiber es a -> Async es a
joinResult f = join f >>= Term

export
cancel : Fiber es a -> Async fs ()
cancel f =
  uncancelable $ \poll => do
    liftIO $ f.cancel
    poll (ignore (join f))

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

||| Asynchronously runs a computation on a new fiber.
|||
||| While we can no longer observe the computation's result, it will still
||| be canceled if the current fiber terminates.
export %inline
background : Async es a -> Async fs ()
background = ignore . start

--------------------------------------------------------------------------------
-- MonadError
--------------------------------------------------------------------------------

export %inline
fail : HSum es -> Async es a
fail = Term . Error

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
handleErrors f x =
  Bind x $ \case
    Succeeded x => Term $ Succeeded x
    Error x     => f x
    Canceled    => Term Canceled

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

export
guaranteeCase : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
guaranteeCase as f =
  uncancelable $ \poll => do
    Bind (poll as) $ \o => Bind (f o) (\_ => Term o)

export %inline
onCancel : Async es a -> Async [] () -> Async es a
onCancel as x = guaranteeCase as $ \case Canceled => x; _ => pure ()

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
bracketCase :
     Async es a
  -> (a -> Async es b)
  -> ((a,Outcome es b) -> Async [] ())
  -> Async es b
bracketCase acquire use release =
  uncancelable $ \poll => do
    res <- poll acquire
    guaranteeCase (use res) (\o => release (res,o))

export %inline
bracket : Async es a -> (a -> Async es b) -> (a -> Async [] ()) -> Async es b
bracket acquire use release =
  bracketCase acquire use (release . fst)

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
raceF : List (Async es (Fiber es a)) -> Async es a
raceF fs = do
  t    <- self
  fibs <- sequence fs
  cancelableAsync (\cb => for_ fibs (\f => f.observe t cb) $> stop t fibs)

  where
    stop : Token -> List (Fiber es a) -> Async [] ()
    stop t fibers = liftIO $ for_ fibers $ \f => f.stopObserving t

||| Alias for `raceF . traverse start`.
export %inline
race : (xs : List $ Async es a) -> Async es a
race = raceF . map start

injections : All f ts -> All (\t => (v : t) -> HSum ts) ts
injections []        = []
injections (x :: xs) = Here :: mapProperty (There .) (injections xs)

||| Runs a heterogeneous list of asynchronous computations in parallel,
||| keeping only the one that finishes first.
export %inline
raceAny : All (Async es) ts -> Async es (HSum ts)
raceAny xs = race . forget $ hzipWith map (injections xs) xs

collectOutcomes : All (Outcome es) ts -> Outcome es (HList ts)
collectOutcomes []                 = Succeeded []
collectOutcomes (Succeeded r :: t) = (r::) <$> collectOutcomes t
collectOutcomes (Error x     :: t) = Error x
collectOutcomes (Canceled    :: t) =
  case collectOutcomes t of
    Error x => Error x
    _       => Canceled

||| Accumulates the results of the given heterogeneous list of
||| fibers in a heterogeneous list.
export
parF : All (Async es . Fiber es) ts -> Async es (HList ts)
parF fs = do
  fibers <- hsequence fs
  hsequence $ mapProperty joinResult fibers

||| Runs the given computations in parallel and collects the outcomes
||| in a heterogeneous list.
export %inline
par : All (Async es) ts -> Async es (HList ts)
par = parF . mapProperty start

export
parTraverse : (a -> Async es b) -> List a -> Async es (List b)
parTraverse f vs = do
  fibers <- traverse (start . f) vs
  traverse joinResult fibers

export covering
runAsyncWith : ExecutionContext => Async es a -> (Outcome es a -> IO ()) -> IO ()

export covering %inline
runAsync : ExecutionContext => Async es a -> IO ()
runAsync as = runAsyncWith as (\_ => pure ())

--------------------------------------------------------------------------------
-- Implementation (Here be Dragons)
--------------------------------------------------------------------------------

-- Properly typed stack of nested `Bind`s plus their cancelability
data Stack : (es,fs : List Type) -> (a,b : Type) -> Type where
  Nil  : Stack es es a a
  (::) :
       (Outcome es a -> Async fs b)
    -> Stack fs gs b c
    -> Stack es gs a c

-- Current stat of a fiber
data FiberState : List Type -> Type -> Type where
  -- The fiber has just been initialized with the asynchronous
  -- computation it is about to run.
  Init        : Async es a -> FiberState es a

  -- The fiber is currently being run on its execution context
  Running     : FiberState es a

  -- The fiber is currently being run on its execution context,
  -- and it has been informed that the result from an asynchronous
  -- function call is ready
  ResultReady : FiberState es a

  -- The fiber produced an outcome and ist now finished.
  Done        : Outcome es a -> FiberState es a

  -- The fiber is awaiting the result from an asynchronous
  -- computation, and is currently not being run.
  Suspended   :
       IORef (Maybe $ Outcome es a)
    -> (onCancel : Maybe $ Async [] ())
    -> (cancelID : Nat)
    -> (cancelStack : List Nat)
    -> Stack es fs a b
    -> FiberState fs b

-- An existential (non-parameterized) wrapper around a `FiberImpl es a`
data AnyFiber : Type

record FiberImpl (es : List Type) (a : Type) where
  constructor FI
  ec        : IORef ExecutionContext
  mutex     : Mutex
  parent    : Maybe AnyFiber
  token     : Token
  callbacks : IORef (SortedMap Token (Outcome es a -> IO ()))
  children  : IORef (SortedMap Token AnyFiber)
  canceled  : IORef Bool
  state     : IORef (FiberState es a)

data AnyFiber : Type where
  AF : FiberImpl es a -> AnyFiber

withLock : FiberImpl es a -> IO b -> IO b
withLock fbr f = do
  mutexAcquire fbr.mutex
  res <- f
  mutexRelease fbr.mutex
  pure res

addChild : Maybe AnyFiber -> FiberImpl fs b -> IO ()
addChild Nothing       _ = pure ()
addChild (Just $ AF q) y =
  withLock q $
    readIORef q.canceled >>= \case
      True  => writeIORef y.canceled True
      False => modifyIORef q.children (insert y.token (AF y))

removeChild : FiberImpl es a -> Token -> IO ()
removeChild fbr tk = withLock fbr (modifyIORef fbr.children $ delete tk)

newFiber :
     ExecutionContext
  -> (parent : Maybe AnyFiber)
  -> (as     : Async es a)
  -> IO (FiberImpl es a)
newFiber ec p as = do
  fbr <- [| FI
              (newIORef ec)
              makeMutex
              (pure p)
              token
              (newIORef empty)
              (newIORef empty)
              (newIORef False)
              (newIORef $ Init as)
         |]
  addChild p fbr
  pure fbr

stopObservingImpl : FiberImpl es a -> Token -> IO ()
stopObservingImpl fbr tk = withLock fbr $ modifyIORef fbr.callbacks (delete tk)

observeImpl :
     FiberImpl es a
  -> Token
  -> (Outcome es a -> IO ())
  -> IO ()
observeImpl fbr tk cb = do
  run <- withLock fbr $
    readIORef fbr.state >>= \case
      Done o => pure (cb o)
      _      => modifyIORef fbr.callbacks (insert tk cb) $> pure ()
  run

covering run :
     {auto ec : ExecutionContext}
  -> Nat
  -> FiberImpl fs b
  -> Async es a
  -> (cancelID : Nat)
  -> (cancelStack : List Nat)
  -> Stack es fs a b
  -> IO ()

-- This function is invoked if
--   a) The fiber was canceled
--   b) The result of a callback is ready
covering resume : FiberImpl es a -> IO ()
resume fbr = do
  -- This might be invoked from several threads, so we
  -- adjust the state and assemble the action to run under
  -- a lock. The action is run after the mutex was released.
  run <- withLock fbr $ do
    readIORef fbr.state >>= \case
      Suspended ref cncl i cs s => do
        -- take over control and make sure no one else does
        writeIORef fbr.state Running
        ec <- readIORef fbr.ec
        readIORef fbr.canceled >>= \case

          -- we are still up and running, so the result in the
          -- mutable reference should be ready
          False => readIORef ref >>= \case
            -- all is well. let's continue
            Just o  => pure (run @{ec} ec.limit fbr (Term o) i cs s)
            -- WTF?? This should not happen, so should we crash?
            Nothing => writeIORef fbr.state (Suspended ref cncl i cs s) $> pure ()

          -- we were canceled so run the cancel hook (if any)
          -- otherwise, just continue and finish the uncancelable parts
          -- IMPORTANT: We will no longer wait for the callback to finish!
          True  => case cncl of
            Just c  =>
              let f := uncancelable $ \_ => Bind c (\_ => Term Canceled)
               in pure (run @{ec} ec.limit fbr f i cs s)
            Nothing => pure (run @{ec} ec.limit fbr (Term Canceled) i cs s)

      Init as => do
        writeIORef fbr.state Running
        ec <- readIORef fbr.ec
        pure (run @{ec} ec.limit fbr as 0 [] [])

      -- we are already running or done, so don't interfere
      _  => pure (pure ())
  run -- actually run the action we got

covering suspend :
     FiberImpl fs b
  -> IORef (Maybe $ Outcome es a)
  -> Maybe (Async [] ())
  -> (cancelID : Nat)
  -> (cancelStack : List Nat)
  -> Stack es fs a b
  -> IO ()
suspend fbr ref cncl i cs s = do
  run <- withLock fbr $ do
    readIORef fbr.state >>= \case
      ResultReady => writeIORef fbr.state (Suspended ref cncl i cs s) $> resume fbr
      Running     => writeIORef fbr.state (Suspended ref cncl i cs s) $> pure ()
      _           => pure (pure ())
  run

covering cancelImpl : FiberImpl es a -> IO ()
cancelImpl fbr = do
  run <- withLock fbr $ do -- make sure no one else adjusts the state
    readIORef fbr.canceled >>= \case
      True  => pure (pure ()) -- we have already been canceled, so that's being take care of
      False => writeIORef fbr.canceled True $> resume fbr
  run

-- We have a result and the fiber can be finalized.
-- This can only be called from a running fiber, so we don't have
-- to check the state here.
covering finalize : FiberImpl es a -> Outcome es a -> IO ()
finalize fbr o = do
  run <- withLock fbr $ do -- make sure no one else adjusts the state
    -- We won the race, so we set the state to "Done" before anybody else does.
    writeIORef fbr.state (Done o)

    -- Read and empty the callbacks...
    cbs <- readIORef fbr.callbacks
    writeIORef fbr.callbacks empty

    -- Read and empty the children...
    chl <- readIORef fbr.children
    writeIORef fbr.children empty

    -- ...and invoke all callbacks and cancel all children
    pure $ do
      for_ fbr.parent (\(AF x) => removeChild x fbr.token)
      for_ cbs (\cb => cb o)
      for_ chl (\(AF x) => cancelImpl x)

  run -- actually run the action we got

observeCancelation : List Nat -> FiberImpl es a -> IO Bool
observeCancelation [] f = withLock f (readIORef f.canceled)
observeCancelation _  _ = pure False

stopUC : List Nat -> List Nat
stopUC (h::t) = t
stopUC []     = []

covering (.fiber) : FiberImpl es a -> Fiber es a
f.fiber = MkFiber f.token (observeImpl f) (stopObservingImpl f) (cancelImpl f)

run n fbr act i cs stck = do
  False <- observeCancelation cs fbr | True => finalize fbr Canceled
  case n of
   0 => ec.submit (run ec.limit fbr act i cs stck)
   S k => case act of
     Term o => case stck of
       f::fs => run k fbr (f o) i cs fs
       []    => finalize fbr o

     Sync io => do
       r <- io
       run k fbr (Term $ toOutcome r) i cs stck

     Start as => do
       child <- newFiber ec (Just $ AF fbr) as
       ec.submit (resume child)
       run k fbr (pure child.fiber) i cs stck

     Shift ec2 => do
       writeIORef fbr.ec ec2 >>
       ec2.submit (run @{ec2} k fbr (pure ()) i cs stck)

     Self => run k fbr (pure fbr.token) i cs stck

     Cancel => do
       withLock fbr (writeIORef fbr.canceled True) >>
       run k fbr (pure ()) i cs stck

     GetEC => run k fbr (pure ec) i cs stck

     Bind x f => run k fbr x i cs (f::stck)

     UC f => run k fbr (Bind (f i) (\o => StopUC >> Term o)) (S i) (i::cs) stck

     APoll j x => case cs of
       h::t =>
          if h == j
             then run k fbr (x <* ContUC h) i t stck
             else run k fbr x i cs stck
       []   => run k fbr x i [] stck

     StopUC => run k fbr (pure ()) i (stopUC cs) stck

     ContUC x => run k fbr (pure ()) i (x::cs) stck

     Asnc reg => do
       ref <- newIORef Nothing
       cnl <- reg $ \o => do
         run <- withLock fbr $ do
           -- test if we won the race and the value is yet unset
           Nothing <- readIORef ref | _ => pure (pure ())
           -- write the value and continue
           writeIORef ref (Just o)
       
           -- Check if the fiber has been canceled. If that's the case,
           -- we are going to be left behind anyway, and we must abort.
           -- (Because the fiber has been canceled, it's current state might
           -- be "Running", and we must not mistake that for us winning the
           -- concurrent race)
           readIORef fbr.canceled >>= \case
             True  => pure (pure ())
             False =>
               -- Check the current fiber state: If it is still at `Running`, we were
               -- so quick (or synchronous) that the fiber had no time to get
               -- suspended. In that case, the fiber will be suspended in a moment
               -- and we inform it that the result is already here.
               readIORef fbr.state >>= \case
                 -- We were quick and the fiber can continue immediately.
                 Running => writeIORef fbr.state ResultReady $> pure()
                 -- The fiber has already been suspended, so it can resume now.
                 _       => pure (resume fbr)
         run
       suspend fbr ref cnl i cs stck

runAsyncWith @{ec} as cb = do
  fib <- newFiber ec Nothing as
  tk  <- token
  observeImpl fib tk cb
  ec.submit (resume fib)
