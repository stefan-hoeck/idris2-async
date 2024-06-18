module IO.Async.ThreadPool

import public Data.Nat
import Data.IORef
import Data.Queue
import Data.Vect
import IO.Async.Fiber
import IO.Async.MVar
import IO.Async.Outcome
import IO.Async.Token
import System.Concurrency

%default total

--------------------------------------------------------------------------------
-- Worker
--------------------------------------------------------------------------------

||| State of a physical worker thread in a thread-pool.
export
record WorkST where
  constructor W
  ||| True, if this worker has been stopped. No new action can be
  ||| enqueued in that case.
  stopped : IORef Bool

  ||| Queue of actions to be run on this thread.
  queue   : IORef (Queue $ IO ())

  ||| Used to inform the thread that a new action has been enqueued.
  cond    : Condition

  ||| Lock for thread safety.
  lock    : Mutex

||| Initialize the state of a worker thread.
export
newWorkST : IO WorkST
newWorkST = [| W (newIORef False) (newIORef empty) makeCondition makeMutex |]

withMutex : Mutex -> (io : Lazy (IO ())) -> IO ()
withMutex m io = mutexAcquire m >> io >> mutexRelease m

namespace WorkST

  ||| Set the `stopped` flag of a worker thread to `True` and
  ||| inform the thread that its state has changed.
  export
  stop : WorkST -> IO ()
  stop w =
    withMutex w.lock (writeIORef w.stopped True >> conditionBroadcast w.cond)

  ||| Enqueue an `IO` action to be processed by a worker thread.
  export %inline
  submit : WorkST -> IO () -> IO ()
  submit w v = do
    withMutex w.lock $ do
      False <- readIORef w.stopped | True => pure ()
      modifyIORef w.queue (flip enqueue v)
      conditionBroadcast w.cond

  covering
  process' : Bool -> WorkST -> IO ()
  process' b w = do
    when b (mutexAcquire w.lock)
    q <- readIORef w.queue
    case dequeue q of
      Nothing => do 
        False <- readIORef w.stopped 
          | True => mutexRelease w.lock
        conditionWait w.cond w.lock
        process' False w
  
      Just (v,q2) => do
        writeIORef w.queue q2
        mutexRelease w.lock
        v
        process' True w
  
  ||| Continuously process enqueued `IO` actions on the current
  ||| thread until the `stopped` flag of the worker state has been
  ||| set to `True`.
  |||
  ||| The thread will be blocked while the queue of `IO` actions
  ||| is empty.
  export covering %inline
  process : WorkST -> IO ()
  process = process' True

||| A fixed-size pool of `n` physical worker threads.
|||
||| Tasks are submited to the worker threads in round-robin
||| fashion: A new task is submitted to the next worker in line,
||| restarting at the beginning when reaching the last worker.
export
record ThreadPool (n : Nat) where
  constructor TP
  tg   : TokenGen
  st   : Vect n WorkST
  ts   : Vect n ThreadID
  curr : MVar (Fin n)

||| Create a new thread pool of `n` worker threads.
export covering
newWorkPool : (n : Nat) -> {auto 0 p : IsSucc n} -> IO (ThreadPool n)
newWorkPool (S m) = do
  tg <- newTokenGen
  ws <- traverse (const newWorkST) (replicate _ Z)
  ts <- traverse (\x => fork $ process x) ws
  TP tg ws ts <$> newMVar last

next : {n : _} -> Fin (S n) -> Fin (S n)
next (FS x) = weaken x
next FZ     = last

namespace ThreadPool

  ||| Sets the `stopped` flag of all worker threads and awaits
  ||| their termination.
  export
  stop : ThreadPool n -> IO ()
  stop (TP _ st ts _) = do
    traverse_ stop st
    traverse_ (\x => threadWait x) ts

  ||| Submit a new `IO` action to be processed by the worker threads
  ||| in a thread pool.
  export %inline
  submit : {n : _} -> ThreadPool (S n) -> IO () -> IO ()
  submit (TP _ st _ curr) io = do
    x <- evalState curr (\y => (next y, y))
    WorkST.submit (index x st) io

||| Create an execution context from a thread pool.
export %inline
ec : {n : _} -> ThreadPool (S n) -> (limit : Nat) -> ExecutionContext
ec wp limit = EC wp.tg (ThreadPool.submit wp) limit

||| Run an asyncrhonous application on a thread pool with
||| `n` physical threads.
|||
||| The calling thread is blocked until the application completes.
export covering
app : (n : Nat) -> {auto 0 _ : IsSucc n} -> Async [] () -> IO ()
app (S m) act = do
  tp <- newWorkPool (S m)
  m  <- makeMutex
  c  <- makeCondition
  runAsyncWith @{ec tp 100} act (\_ => conditionBroadcast c)
  mutexAcquire m
  conditionWait c m
  ThreadPool.stop tp
