||| A pool of a fixed number of worker threads, each operating on its own
||| work queue.
|||
||| Idle threads will try and take work packages from other threads
||| (work-stealing).
|||
||| Each thread is responsible for scheduling and running an arbitrary number
||| of `Fiber`s, as well as taking care of registered timers, signal handlers,
||| and file polling.
module IO.Async.Loop.Posix

import public Data.Nat
import public IO.Async
import public IO.Async.Loop
import public IO.Async.Loop.PollH
import public IO.Async.Loop.SignalH
import public IO.Async.Loop.TimerH

import Control.Monad.Elin

import Data.Array.Core as AC
import Data.Array.Mutable
import Data.Linear.Traverse1
import Data.Queue
import Data.Vect

import IO.Async.Internal.Ref
import IO.Async.Loop.Poller
import IO.Async.Loop.SignalST
import IO.Async.Loop.TimerST
import IO.Async.Signal

import System
import System.Posix.File.Prim
import System.Posix.Poll.Prim
import System.Posix.Pthreads.Prim
import System.Posix.Limits

%default total

--------------------------------------------------------------------------------
-- Loop State
--------------------------------------------------------------------------------

POLL_ITER : Nat
POLL_ITER = 16

-- State of a physical worker thread in a thread-pool.
export
record Poll where
  constructor W
  ||| Number of worker threads in the pool
  size     : Nat

  ||| Index of the worker thread corresponding to this state
  me       : Fin size

  ||| Reference indicating whether the pool is still alive
  alive    : IORef Bool

  ||| Recently ceded work package. Since switching threads is
  ||| a costly operation, we want to prevent this from being
  ||| rescheduled (stolen by other workers) when this worker's
  ||| queue is empty.
  ceded    : IORef (Maybe $ Package Poll)

  ||| Work queues of all worker threads
  queues   : IOArray size (Queue $ Package Poll)

  ||| The state used for polling file descriptors
  poller   : Poller

  ||| Remaining number of stealers. To reduce contention,
  ||| not all idle workers will be allowed to steal work
  ||| at the same time
  stealers : IORef Nat

  ||| State for schedule actions
  timer : Timer

  ||| State for the signal handler
  signals : Sighandler

  ||| Mutex used for sleeping
  lock    : MutexT

  ||| Condition used for sleeping
  cond    : CondT

public export
0 Task : Type
Task = Package Poll

-- initialize the state of a worker thread.
workST :
     {n : Nat}
  -> Fin n
  -> (poll     : Poller)
  -> IOArray n (Queue Task)
  -> (stealers : IORef Nat)
  -> IO Poll
workST me poll queues stealers =
  runIO $ \t =>
    let alive # t := ref1 True t
        ceded # t := ref1 Nothing t
        tim   # t := TimerST.timer t
        sigh  # t := sighandler t
        lock  # t := dieOnErr (mkmutex MUTEX_NORMAL) t
        cond  # t := dieOnErr mkcond t
     in W n me alive ceded queues poll stealers tim sigh lock cond # t

release : Poll -> IO1 ()
release p t =
  let _ # t := ffi (destroyCond p.cond) t
   in ffi (destroyMutex p.lock) t

--------------------------------------------------------------------------------
-- Work Loop
--------------------------------------------------------------------------------

nextFin : {n : _} -> Fin n -> Fin n
nextFin FZ     = last
nextFin (FS x) = weaken x

parameters (s : Poll)

  -- appends the currently ceded task (if any) to the work queue,
  -- because we have other work to do
  %inline
  uncede : IO1 ()
  uncede t =
    let Just tsk # t := read1 s.ceded t | Nothing # t => () # t
        _        # t := write1 s.ceded Nothing t
     in enqAt s.queues s.me tsk t

  -- tries to steal a task from another worker
  steal : Fin s.size -> Nat -> IO1 (Maybe Task)
  steal x 0     t = Nothing # t
  steal x (S k) t =
    case deqAt s.queues x t of
      Nothing  # t => steal (nextFin x) k t
      Just tsk # t =>
       let _ # t := write1 tsk.env s t
        in Just tsk # t

  -- Looks for the next task to run. If possible, this will be the
  -- last ceded task of this work loop, unless our queue is non-empty,
  -- in which case the ceded task has to be appended to the queue.
  --
  -- If there is no task, we go stealing from other work loops unless
  -- too many stealers are already active.
  %inline
  next : IO1 (Maybe Task)
  next t =
    case deqAt s.queues s.me t of
      Nothing  # t => case read1 s.ceded t of
        Nothing # t => case casupdate1 s.stealers (\x => (pred x, x)) t of
          0   # t => Nothing # t
          S k # t =>
            let tsk # t := steal (nextFin s.me) (pred s.size) t
                _   # t := casmod1 s.stealers S t
             in tsk # t
        tsk     # t => let _ # t := write1 s.ceded Nothing t in tsk # t
      tsk # t => let _ # t := uncede t in tsk # t

  -- Main worker loop. If `cpoll` is at zero, this indicates that we should
  -- poll at this iteration. Otherwise we look for the next task to run.
  -- If there is none, we go to sleep (that is, we `poll` with a timeout
  -- of 1 ms).
  covering
  loop : Nat -> IO1 ()
  loop cpoll t =
    case read1 s.alive t of
      False # t => () # t
      True  # t => case cpoll of
        0   =>
         let _ # t := checkSignals s.signals t
          in loop POLL_ITER t
        S k =>
         let r # t := runDueTimers s.timer t
          in case next t of
               Just tsk # t => let _ # t := tsk.act t in loop k t
               Nothing  # t =>
                 let _ # t := checkSignals s.signals t
                     _ # t := dieOnErr (lockMutex s.lock) t
                     _ # t := dieOnErr (condTimedwait s.cond s.lock 2.ms) t
                     _ # t := dieOnErr (unlockMutex s.lock) t
                  in loop POLL_ITER t

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
PollH Poll where
  primPoll s = s.poller.pollFile

export %inline
TimerH Poll where
  primWait s dur f = schedule s.timer dur f

export %inline
SignalH Poll where
  primOnSignals s sigs f = await s.signals sigs (f . Right)

--------------------------------------------------------------------------------
-- ThreadPool
--------------------------------------------------------------------------------

||| A fixed-size pool of `n` physical worker threads.
|||
||| Tasks are submited to the worker threads in round-robin
||| fashion: A new task is submitted to the next worker in line,
||| restarting at the beginning when reaching the last worker.
export
record ThreadPool where
  constructor TP
  size    : Nat
  ids     : Vect size ThreadID
  pollid  : ThreadID
  workers : Vect (S size) Poll

stop : ThreadPool -> IO ()
stop tp = runIO $ traverse1_ (\w => write1 w.alive False) tp.workers

submit : Task -> IO1 ()
submit p t =
  let st # t := read1 p.env t
      _  # t := enqAt st.queues st.me p t
   in dieOnErr (condSignal st.cond) t

cede : Task -> IO1 ()
cede p t =
  let st # t := read1 p.env t
   in write1 st.ceded (Just p) t

workSTs :
     {n : _}
  -> (poll : Poller)
  -> IOArray n (Queue Task)
  -> (stealers : IORef Nat)
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> IO (Vect k Poll)
workSTs poll qs stealers 0     = pure []
workSTs poll qs stealers (S k) = do
  w  <- workST (natToFinLT k) poll qs stealers
  ws <- workSTs poll qs stealers k
  pure (w::ws)

half : Nat -> Nat
half n = cast (cast n `div` (the Integer 2))

covering
pollLoop : (alive : Ref World Bool) -> Poller -> IO1 ()
pollLoop ref p t =
  let True # t := read1 ref t | _ # t => p.release t
      _    # t := p.pollWait 2.ms t
   in pollLoop ref p t

||| Create a new thread pool of `n` worker threads and additional
covering
mkThreadPool :
     (n : Subset Nat IsSucc)
  -> (mkPoll : IO1 Poller)
  -> IO (ThreadPool, EventLoop Poll)
mkThreadPool (Element (S k) _) mkPoll = do
  qs <- marray (S k) (Queue.empty {a = Package Poll})
  ss <- newref (half $ S k)
  pl <- runIO mkPoll
  ws <- workSTs pl qs ss (S k)
  ts <- traverse (\x => fork (runIO $ loop x POLL_ITER)) (tail ws)
  pi <- fork (runIO $ pollLoop (head ws).alive pl)
  let tp := TP k ts pi ws
  pure (tp, EL submit cede (head ws))

toIO : Elin World [Errno] () -> IO ()
toIO = ignore . runElinIO

||| Starts an epoll-based event loop and runs the given async
||| program to completion.
|||
||| `n`    : Number of threads to use
||| `sigs` : The signals to block while running the program.
|||          These are typically the ones dealt with as part of `prog`
||| `prog` : The program to run
export covering
app :
     (n      : Subset Nat IsSucc)
  -> (sigs   : List Signal)
  -> (mkPoll : IO1 Poller)
  -> (prog   : Async Poll [] ())
  -> IO ()
app n sigs mkPoll prog = do
  toIO $ sigprocmask SIG_BLOCK sigs
  (tp,el) <- mkThreadPool n mkPoll
  runAsyncWith 1024 el prog (\_ => putStrLn "Done. Shutting down" >> stop tp)
  runIO (loop (head tp.workers) POLL_ITER)
  traverse_ (\x => threadWait x) tp.ids
  traverse_ (\w => runIO (release w)) tp.workers
  threadWait tp.pollid
  usleep 100

||| Reads environment variable `IDRIS2_ASYNC_THREADS` and returns
||| the number of threads to use. Default: 2.
export
asyncThreads : IO (Subset Nat IsSucc)
asyncThreads = do
  s <- getEnv "IDRIS2_ASYNC_THREADS"
  pure $ case cast {to = Nat} <$> s of
    Just (S k) => Element (S k) %search
    _          => Element 2 %search

||| Simplified version of `app`.
|||
||| This uses the posix-compatible `poll` call for polling files. For
||| a faster poller - especially when polling hundreds or thousands of
||| file descriptors at a time - consider using `IO.Async.Loop.Epoll.epollApp`.
|||
||| We use environment variable `IDRIS2_ASYNC_THREADS` to determine the
||| number of threads to use (default: 2) and cancel the running program
||| on receiving `SIGINT`. Other signals are not supported.
export covering
simpleApp : Async Poll [] () -> IO ()
simpleApp prog = do
  n <- asyncThreads
  app n [SIGINT] posixPoller cprog

  where
    cprog : Async Poll [] ()
    cprog =
      race_
        [ prog
        , dropErrs {es = [Errno]} $ onSignal SIGINT (pure ())
        ]
