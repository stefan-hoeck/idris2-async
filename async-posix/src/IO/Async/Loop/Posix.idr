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
import Data.List
import Data.Vect

import IO.Async.Internal.Ref
import IO.Async.Loop.Poller
import IO.Async.Loop.Queue
import IO.Async.Loop.SignalST
import IO.Async.Loop.TimerST
import IO.Async.Signal

import System
import System.Concurrency
import System.Posix.File.Prim
import System.Posix.Poll.Prim
import System.Posix.Limits

%default total

--------------------------------------------------------------------------------
-- Poll
--------------------------------------------------------------------------------

public export
0 Task : Type

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

  ||| Work queue of this worker
  queue    : IORef (Queue Task)

  ||| Work queues of all worker threads
  workers  : IArray size Poll

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
  lock    : Mutex

  ||| Condition used for sleeping
  cond    : Condition

Task = FbrState Poll

-- initialize the state of a worker thread.
workST :
     {n : Nat}
  -> Fin n
  -> (poll     : Poller)
  -> (workers  : IArray n Poll)
  -> (stealers : IORef Nat)
  -> IO Poll
workST me poll workers stealers =
  runIO $ \t =>
    let alive # t := ref1 True t
        tim   # t := TimerST.timer t
        sigh  # t := sighandler t
        que   # t := ref1 (queueOf Task) t
        lock  # t := ioToF1 makeMutex t
        cond  # t := ioToF1 makeCondition t
     in W n me alive que workers poll stealers tim sigh lock cond # t

release : Poll -> IO1 ()
release p t = () # t
  -- let _ # t := ffi (destroyCond p.cond) t
  --  in ffi (destroyMutex p.lock) t

debug : Lazy String -> IO1 ()
debug s t = () # t
-- debug s = ioToF1 (putStrLn s)

submit : Poll -> Task -> IO1 ()
submit st p t =
  let _    # t := debug "submitting a fiber to \{show st.me}" t
      True # t := enq st.queue p t | False # t => () # t
      _    # t := debug "waking up \{show st.me}" t
      _    # t := ioToF1 (mutexAcquire st.lock) t
      _    # t := ioToF1 (conditionSignal st.cond) t
   in ioToF1 (mutexRelease st.lock) t

export %inline covering
EventLoop Poll where
  spawn = submit
  limit = 1024

--------------------------------------------------------------------------------
-- Work Loop
--------------------------------------------------------------------------------

nextFin : {n : _} -> Fin n -> Fin n
nextFin FZ     = last
nextFin (FS x) = weaken x

sleepDuration : Integer -> Int -- Clock Duration
sleepDuration 0 = 2_000
sleepDuration n = (min (cast $ n `div` 1000) 2_000) -- at most two milli seconds

parameters (s : Poll)

  -- tries to steal a task from another worker
  stealTasks : Fin s.size -> Nat -> IO1 (Maybe Task)
  stealTasks x 0     t =
   let _ # t := debug "\{show s.me} could not steal anything" t
    in Nothing # t
  stealTasks x (S k) t =
    case steal (queue $ at s.workers x) t of
      Nothing # t => stealTasks (nextFin x) k t
      Just h  # t =>
       let _ # t := debug "\{show s.me} stole a fiber from \{show x} " t
        in Just h # t

  -- Looks for the next task to run. If possible, this will be the
  -- last ceded task of this work loop, unless our queue is non-empty,
  -- in which case the ceded task has to be appended to the queue.
  --
  -- If there is no task, we go stealing from other work loops unless
  -- too many stealers are already active.
  %inline
  next : IO1 (Maybe Task)
  next t =
    case deq s.queue t of
      Nothing # t => case dec s.stealers t of
        False # t =>
         let _ # t := debug "\{show s.me} enough stealers are active" t
          in Nothing # t
        True  # t =>
         let _ # t := debug "\{show s.me} start stealing" t 
             tsk # t := stealTasks (nextFin s.me) (pred s.size) t
             _   # t := Queue.inc s.stealers t
          in tsk # t
      tsk # t =>
       let _   # t := debug "\{show s.me} still got work to do" t
        in tsk # t

  runTask : FbrState Poll -> IO1 ()
  runTask fst t =
    case runFbr s fst t of
      Cont fst2 # t => let _ # t := enq s.queue fst2 t in () # t
      Done      # t => () # t

  -- Main worker loop. If `cpoll` is at zero, this indicates that we should
  -- poll at this iteration. Otherwise we look for the next task to run.
  -- If there is none, we go to sleep (that is, we `poll` with a timeout
  -- of 1 ms).
  covering
  loop : Nat -> IO1 ()
  loop cpoll t =
    -- first we check if the system is still alive and running
    case read1 s.alive t of
      -- Evaluation has ended. Time to shut down.
      False # t => () # t

      -- Still alive, so let's go.
      True  # t => case cpoll of

        -- If it's time for polling, we check our signal handlers
        -- and continue.
        0   =>
         let _ # t := checkSignals s.signals t
          in loop POLL_ITER t

        -- No time for polling. Check timers and get the next task to run -
        -- either by taking the head of our own queue or by stealing from
        -- another queue.
        S k =>
         let r # t := runDueTimers s.timer t
          in case next t of
               Just tsk # t => let _ # t := runTask tsk t in loop k t
               Nothing  # t =>
                let _ # t := checkSignals s.signals t
                    _ # t := ioToF1 (mutexAcquire s.lock) t
                 in case deqAndSleep s.queue t of
                      Just tsk # t =>
                        let _ # t := ioToF1 (mutexRelease s.lock) t
                            _ # t := runTask tsk t
                         in loop POLL_ITER t 
                      Nothing  # t =>
                       let d     := sleepDuration r
                           _ # t := debug "\{show s.me} sleeping for \{show d} us" t
                           _ # t := ioToF1 (conditionWaitTimeout s.cond s.lock  d) t
                           _ # t := ioToF1 (mutexRelease s.lock) t
                        in loop POLL_ITER t

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
PollH Poll where
  threadId s = cast s.me
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

workSTs :
     {n : _}
  -> (poll : Poller)
  -> IOArray n Poll 
  -> IArray n Poll 
  -> (stealers : IORef Nat)
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> IO (Vect n Poll)
workSTs poll mps ips stealers 0     = pure (toVect ips)
workSTs poll mps ips stealers (S k) = do
  w  <- workST (natToFinLT k) poll ips stealers
  runIO $ setNat mps k w
  workSTs poll mps ips stealers k

covering
pollLoop : (alive : Ref World Bool) -> Poller -> IO1 ()
pollLoop ref p t =
  let True # t := read1 ref t | _ # t => p.release t
      _    # t := p.pollWait 10.ms t
   in pollLoop ref p t

||| Create a new thread pool of `n` worker threads and additional
covering
mkThreadPool :
     (n : Subset Nat IsSucc)
  -> (mkPoll : IO1 Poller)
  -> IO ThreadPool
mkThreadPool (Element (S k) _) mkPoll = do
  ps <- unsafeMArray {a = Poll} (S k)
  is <- runIO (unsafeFreeze ps)
  ss <- newref (S Z)
  pl <- runIO mkPoll
  ws <- workSTs pl ps is ss (S k)
  ts <- traverse (\x => fork (runIO $ loop x POLL_ITER)) (tail ws)
  pi <- fork (runIO $ pollLoop (head ws).alive pl)
  pure $ TP k ts pi ws

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
  runIO (dieOnErr $ addFlags Stdin O_NONBLOCK)
  tp <- mkThreadPool n mkPoll
  runAsyncWith (head tp.workers) prog (\_ => putStrLn "Done. Shutting down" >> stop tp)
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
||| on receiving `SIGINT`.
|||
||| By default, only `SIGINT` is masked, to handle other signals
||| within your program, give `{sigs = [...]}` as the first
||| argument. One of the signals must be SIGINT, which is enforced by
||| the `Has SIGINT sigs` constraint.
export covering
simpleApp
  : {default [SIGINT] sigs : List Signal}
  -> Has SIGINT sigs
  => Async Poll [] ()
  -> IO ()
simpleApp {sigs} prog = do
  n <- asyncThreads
  app n sigs posixPoller cprog

  where
    cprog : Async Poll [] ()
    cprog =
      race_
        [ prog
        , dropErrs {es = [Errno]} $ onSignal SIGINT (pure ())
        ]
