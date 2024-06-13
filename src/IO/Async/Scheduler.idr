module IO.Async.Scheduler

import Data.IORef
import IO.Async.Fiber
import IO.Async.MVar
import IO.Async.Outcome
import System.Concurrency
import System.Clock
import System

%default total

--------------------------------------------------------------------------------
-- Scheduler Entry
--------------------------------------------------------------------------------

record Entry where
  constructor E
  {0 res   : Type}
  {0 errs  : List Type}
  rem      : Integer
  val      : Lazy res
  act      : Outcome errs res -> IO ()
  canceled : MVar Bool

cancel : Entry -> IO ()
cancel e = e.act Canceled

send : Entry -> IO ()
send e = do
  readMVar e.canceled >>= \case
    True  => e.act Canceled
    False => e.act (Succeeded e.val)

||| State of a physical scheduler thread.
export
record Scheduler where
  [noHints]
  constructor S
  ||| True, if this scheduler has been stopped. No new action can be
  ||| enqueued in that case.
  stopped : IORef Bool

  ||| System clock on previous run
  prev    : IORef (Maybe Integer)

  ||| Queue of actions to be run
  entries : IORef (SnocList Entry)

  ||| Used to inform the thread that a new action has been enqueued.
  cond    : Condition

  ||| Lock for thread safety.
  lock    : Mutex

||| Initialize the state of a scheduler.
export
newSchedulerST : IO Scheduler
newSchedulerST =
  [| S (newIORef False)
       (newIORef Nothing)
       (newIORef [<])
       makeCondition
       makeMutex
  |]

withMutex : Mutex -> (io : Lazy (IO a)) -> IO a
withMutex m io = do
  mutexAcquire m
  res <- io
  mutexRelease m
  pure res

||| Set the `stopped` flag of a worker thread to `True` and
||| inform the thread that its state has changed.
export
stop : Scheduler -> IO ()
stop w =
  withMutex w.lock (writeIORef w.stopped True >> conditionBroadcast w.cond)

||| Enqueue an `IO` action to be processed by a worker thread.
export %inline
submit :
     Scheduler
  -> (ns : Nat)
  -> Lazy a
  -> (Outcome es a -> IO ())
  -> IO (IO ())
submit w d v f = do
  withMutex w.lock $ do
    False <- readIORef w.stopped | True => f (Canceled) $> pure ()
    var   <- newMVar False
    modifyIORef w.entries (:< E (cast d) v f var)
    conditionBroadcast w.cond
    pure $ writeMVar var True

stopScheduler : Scheduler -> IO ()
stopScheduler w = do
  sx <- readIORef w.entries
  traverse_ cancel (sx <>> [])

checkSchedule :
     (done,active : List Entry)
  -> (entries     : SnocList Entry)
  -> (delta       : Integer)
  -> IO (List Entry, List Entry)
checkSchedule done active [<]       d = pure (done,active)
checkSchedule done active (sx :< x) d = do
  b <- readMVar x.canceled
  let newRem := x.rem - d
  if b || newRem <= 0
     then checkSchedule (x::done) active sx d
     else checkSchedule done ({rem := newRem} x :: active) sx d

nanos : Clock t -> Integer
nanos c = seconds c * 1_000_000_000 + nanoseconds c

covering
process' : Bool -> Scheduler -> IO ()
process' b w = do
  when b (mutexAcquire w.lock)
  False <- readIORef w.stopped
    | True => mutexRelease w.lock >> stopScheduler w
  readIORef w.entries >>= \case
    [<] => do
      writeIORef w.prev Nothing
      conditionWait w.cond w.lock
      process' False w
    
    sx => do
      c <- nanos <$> clockTime Monotonic
      d <- maybe 0 (\x => c - x) <$> readIORef w.prev
      writeIORef w.prev $ Just c
      (done,active) <- checkSchedule [] [] sx d
      writeIORef w.entries ([<] <>< active)
      mutexRelease w.lock
      traverse_ send done
      process' True w

||| Continuously process enqueued `IO` actions on the current
||| thread until the `stopped` flag of the worker state has been
||| set to `True`.
|||
||| The thread will be blocked while the queue of `IO` actions
||| is empty.
export covering %inline
process : Scheduler -> IO ()
process = process' True

--------------------------------------------------------------------------------
-- Delayed Computations
--------------------------------------------------------------------------------

||| Delay a computation by the given number of nanoseconds.
export
delay : (s : Scheduler) => (nanos : Nat) -> Async es a -> Async es a
delay nanos act = cancelableAsync (map liftIO . submit s nanos act) >>= id

||| Delay a computation by the given number of nanoseconds.
export
sleep : (s : Scheduler) => (nanos : Nat) -> Async es ()
sleep nanos = delay nanos (pure ())

||| Converts a number of seconds to nanoseconds
export
(.s) : Nat -> Nat
n.s = n * 1_000_000_000

||| Converts a number of milliseconds to nanoseconds
export
(.ms) : Nat -> Nat
n.ms = n * 1_000_000

||| Converts a number of microseconds to nanoseconds
export
(.us) : Nat -> Nat
n.us = n * 1_000
