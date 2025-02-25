module IO.Async.Loop.Epoll

import public Data.Nat
import Control.Monad.Elin
import Data.Array.Core as AC
import Data.Array.Mutable
import Data.Bits
import Data.DPair
import Data.Linear.Traverse1
import Data.Queue
import Data.Vect

import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Token
import IO.Async.Loop.Poller
import IO.Async.Loop.SignalST
import IO.Async.Loop.TimerST
import IO.Async.Signal

import public IO.Async
import public IO.Async.Loop
import public IO.Async.Epoll
import public IO.Async.Loop.TimerH
import public IO.Async.Loop.SignalH

import System
import System.Linux.Signalfd.Prim
import System.Linux.Timerfd.Prim
import System.Posix.File.Prim
import System.Posix.Limits

%default total

--------------------------------------------------------------------------------
-- EpollST
--------------------------------------------------------------------------------

POLL_ITER : Nat
POLL_ITER = 16

-- State of a physical worker thread in a thread-pool.
export
record EpollST where
  constructor W
  ||| Number of worker threads in the pool
  size     : Nat

  ||| Index of the worker thread corresponding to this state
  me       : Fin size

  ||| Reference indicating whether the pool is still alive
  alive    : IORef Alive

  ||| Recently ceded work package. Since switching threads is
  ||| a costly operation, we want to prevent this from being
  ||| rescheduled (stolen by other workers) when this worker's
  ||| queue is empty.
  ceded    : IORef (Maybe $ Package EpollST)

  ||| Work queues of all worker threads
  queues   : IOArray size (Queue $ Package EpollST)

  ||| The `epoll` file descriptor used for polling
  poller   : Poller

  ||| Remaining number of stealers. To reduce contention,
  ||| not all idle workers will be allowed to steal work
  ||| at the same time
  stealers : IORef Nat

  ||| State for schedule actions
  timer : Timer

  ||| State for the signal handler
  signals : Sighandler

public export
0 Task : Type
Task = Package EpollST

-- initialize the state of a worker thread.
workST :
     {n : Nat}
  -> Fin n
  -> (maxFiles : Nat)
  -> IOArray n (Queue Task)
  -> (stealers : IORef Nat)
  -> IO EpollST
workST me maxFiles queues stealers =
  runIO $ \t =>
    let alive # t := ref1 Run t
        ceded # t := ref1 Nothing t
        poll  # t := Poller.poller maxFiles t
        tim   # t := TimerST.timer t
        sigh  # t := sighandler t
     in W n me alive ceded queues poll stealers tim sigh # t

--------------------------------------------------------------------------------
-- Work Loop
--------------------------------------------------------------------------------

nextFin : {n : _} -> Fin n -> Fin n
nextFin FZ     = last
nextFin (FS x) = weaken x

pollDuration : Integer -> Clock Duration
pollDuration 0 = 1.ms
pollDuration n = (cast $ min n 1_000_000).ns -- at most one milli second

parameters (s : EpollST)

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
      Stop # t => () # t
      Run  # t => case cpoll of
        0   =>
          let _ # t := poll s.poller t
              _ # t := checkSignals s.signals t
           in loop POLL_ITER t
        S k =>
         let r # t := runDueTimers s.timer t
          in case next t of
               Just tsk # t => let _ # t := tsk.act t in loop k t
               Nothing  # t =>
                 let _ # t := checkSignals s.signals t
                     _ # t := pollWait s.poller (pollDuration r) t
                  in loop POLL_ITER t

release : EpollST -> IO ()
release s = do
  free s.poller.events
  fromPrim (close' s.poller.epoll)

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
Epoll EpollST where
  primEpoll s = pollFile s.poller

export %inline
TimerH EpollST where
  primWait s dur f = schedule s.timer dur f

export %inline
SignalH EpollST where
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
  workers : Vect (S size) EpollST

stop : ThreadPool -> IO ()
stop tp = runIO $ traverse1_ (\w => write1 w.alive Stop) tp.workers

submit : Task -> IO1 ()
submit p t =
  let st # t := read1 p.env t
   in enqAt st.queues st.me p t

cede : Task -> IO1 ()
cede p t =
  let st # t := read1 p.env t
   in write1 st.ceded (Just p) t

workSTs :
     {n : _}
  -> (maxFiles : Nat)
  -> IOArray n (Queue Task)
  -> (stealers : IORef Nat)
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> IO (Vect k EpollST)
workSTs maxFiles qs stealers 0     = pure []
workSTs maxFiles qs stealers (S k) = do
  w  <- workST (natToFinLT k) maxFiles qs stealers
  ws <- workSTs maxFiles qs stealers k
  pure (w::ws)

half : Nat -> Nat
half n = cast (cast n `div` (the Integer 2))

||| Create a new thread pool of `n` worker threads and additional
covering
mkThreadPool :
     (n : Subset Nat IsSucc)
  -> IO (ThreadPool, EventLoop EpollST)
mkThreadPool (Element (S k) _) = do
  qs <- marray (S k) (Queue.empty {a = Package EpollST})
  let mfs := sysconf SC_OPEN_MAX
  ss <- newref (half $ S k)
  ws <- workSTs (cast mfs) qs ss (S k)
  ts <- traverse (\x => fork (runIO $ loop x POLL_ITER)) (tail ws)
  let tp := TP k ts ws
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
     (n    : Subset Nat IsSucc)
  -> (sigs : List Signal)
  -> (prog : Async EpollST [] ())
  -> IO ()
app n sigs prog = do
  toIO $ sigprocmask SIG_BLOCK sigs
  (tp,el) <- mkThreadPool n
  tg <- newTokenGen
  runAsyncWith 1024 el prog (\_ => putStrLn "Done. Shutting down" >> stop tp)
  runIO (loop (head tp.workers) POLL_ITER)
  traverse_ (\x => threadWait x) tp.ids
  traverse_ release tp.workers
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
||| We use environment variable `IDRIS2_ASYNC_THREADS` to determine the
||| number of threads to use (default: 2) and cancel the running program
||| on receiving `SIGINT`. Other signals are not supported.
export covering
simpleApp : Async EpollST [] () -> IO ()
simpleApp prog = do
  n <- asyncThreads
  app n [SIGINT] cprog

  where
    cprog : Async EpollST [] ()
    cprog =
      race_
        [ prog
        , dropErrs {es = [Errno]} $ onSignal SIGINT (pure ())
        ]
