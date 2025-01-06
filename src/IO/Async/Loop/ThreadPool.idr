||| A pool of a fixed number of worker threads, each operating on its own
||| work queue.
|||
||| Idle threads will try and take work packages from other threads
||| (work-stealing). However, work-stealing requires synchronization and
||| communication between workers, so it comes with a considerable overhead.
|||
||| After certain intervals, a worker moves one of its tasks to its
||| "shared" queue. Workers without active tasks will take a task from
||| their own shared queue or from a shared queue of one of their
||| neighbours. If no such task can be found, they sleep (become idle)
||| for a short amount of time.
module IO.Async.Loop.ThreadPool

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop

import public Data.Nat
import public IO.Async
import public IO.Async.Loop

import IO.Async.Internal.Ref
import IO.Async.Internal.Timer
import IO.Async.Internal.Token
import Data.Linear.Traverse1
import Data.List
import Data.List1
import Data.Queue
import Data.Vect

import Data.Array.Mutable
import System

%default total

--------------------------------------------------------------------------------
-- Worker
--------------------------------------------------------------------------------

-- State of a physical worker thread in a thread-pool.
export
record WorkST where
  constructor W
  size   : Nat
  me     : Fin size
  alive  : IORef Alive
  empty  : IORef Bool
  queues : IOArray size (Queue $ Package WorkST)

public export
0 Task : Type
Task = Package WorkST

-- initialize the state of a worker thread.
workST :
     {n : Nat}
  -> Fin n
  -> IOArray n (Queue Task)
  -> IO WorkST
workST me queues =
  runIO $ \t =>
    let empty # t := refIO True t
        alive # t := refIO Run t
     in (W n me alive empty queues) # t

next : {n : _} -> Fin n -> Fin n
next FZ     = last
next (FS x) = weaken x

covering
steal : (s : WorkST) -> Fin s.size -> Nat -> IO1 ()

covering
loop : WorkST -> Package WorkST -> IO1 ()
loop s pkg t =
  let Run    # t := read1 s.alive t | _ # t => () # t
      _      # t := write1 pkg.env s t
      _      # t := pkg.act t
   in steal s s.me s.size t

steal s x 0     t =
  let _ # t := ioToF1 (usleep 1000) t
   in steal s s.me s.size t
steal s x (S k) t =
  case deqAt s.queues x t of
    Nothing  # t => steal s (next x) k t
    Just pkg # t => loop s pkg t

||| A fixed-size pool of `n` physical worker threads.
|||
||| Tasks are submited to the worker threads in round-robin
||| fashion: A new task is submitted to the next worker in line,
||| restarting at the beginning when reaching the last worker.
export
record ThreadPool where
  constructor TP
  size    : Nat
  ids     : Vect (S size) ThreadID
  workers : Vect (S size) WorkST

||| Sets the `stopped` flag of all worker threads and awaits
||| their termination.
stop : ThreadPool -> IO ()
stop tp = do
  runIO $ traverse1_ (\w => write1 w.alive Stop) tp.workers
  traverse_ (\x => threadWait x) tp.ids

||| Submit a new `IO` action to be processed by the worker threads
||| in a thread pool.
submit : Package WorkST -> IO1 ()
submit p t =
  let st # t := read1 p.env t
   in enqAt st.queues st.me p t

covering
cede : Package WorkST -> IO1 ()
cede p t =
  let st # t := read1 p.env t
   in case deqAt st.queues st.me t of
        Nothing  # t => loop st p t
        Just pkg # t =>
          let _ # t := enqAt st.queues st.me p t
           in loop st pkg t

workSTs :
     IOArray n (Queue $ Package WorkST)
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> IO (Vect k WorkST)

||| Create a new thread pool of `n` worker threads and additional thread
||| for scheduling timed tasks.
covering
mkThreadPool :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> IO (EventLoop WorkST, IO ())
mkThreadPool (S k) = do
  qs <- newIOArray (S k) (Queue.empty {a = Package WorkST})
  ws <- workSTs qs (S k)
  ts <- traverse (\x => fork (runIO $ steal x x.me x.size)) ws
  let tp := TP k ts ws
  pure (EL submit cede (head ws), stop tp)

export covering
app : (n : Nat) -> {auto 0 p : IsSucc n} -> Async WorkST [] () -> IO ()
app n act = do
  (el,close) <- mkThreadPool n
  m  <- primIO mkMutex
  c  <- primIO makeCondition
  tg <- newTokenGen
  runAsyncWith 1024 el act (\_ => putStrLn "Done. Shutting down" >> fromPrim (conditionBroadcast c))
  primIO $ acqMutex m
  primIO $ conditionWait c m
  close
  usleep 100
