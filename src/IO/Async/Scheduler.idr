module IO.Async.Scheduler

import Data.IORef
import IO.Async.MVar
import IO.Async.Outcome
import System.Concurrency
import System.Clock
import System

%default total

record Entry where
  constructor E
  {0 res   : Type}
  {0 errs  : List Type}
  rem      : Integer
  val      : Lazy res
  act      : Outcome errs res -> IO ()
  canceled : MVar Bool

||| State of a physical scheduler thread.
export
record SchedulerST where
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
newSchedulerST : IO SchedulerST
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
stop : SchedulerST -> IO ()
stop w =
  withMutex w.lock (writeIORef w.stopped True >> conditionBroadcast w.cond)

||| Enqueue an `IO` action to be processed by a worker thread.
export %inline
submit :
     SchedulerST
  -> (ns : Nat)
  -> (Outcome es a -> IO ())
  -> Lazy a
  -> IO (IO ())
submit w d f v = do
  withMutex w.lock $ do
    False <- readIORef w.stopped | True => f (Canceled) $> pure ()
    var   <- newMVar False
    modifyIORef w.entries (:< E (cast d) v f var)
    conditionBroadcast w.cond
    pure $ writeMVar var True

-- covering
-- process' : Bool -> SchedulerST -> IO ()
-- process' b w = do
--   when b (mutexAcquire w.lock)
--   map (<>> []) (readIORef w.queue) >>= \case
--     [] => do
--       False <- readIORef w.stopped | True => mutexRelease w.lock
--       writeIORef w.prev Nothing
--       conditionWait w.cond w.lock
--       process' False w
-- 
--     xs => ?fooo
--       -- writeIORef w.queue q2
--       -- mutexRelease w.lock
--       -- v
--       -- process' True w
-- 
-- ||| Continuously process enqueued `IO` actions on the current
-- ||| thread until the `stopped` flag of the worker state has been
-- ||| set to `True`.
-- |||
-- ||| The thread will be blocked while the queue of `IO` actions
-- ||| is empty.
-- export covering %inline
-- process : SchedulerST -> IO ()
-- process = process' True
