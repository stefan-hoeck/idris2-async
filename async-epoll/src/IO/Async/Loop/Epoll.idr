module IO.Async.Loop.Epoll

import public Data.Nat
import Data.Array.Core as AC
import Data.Array.Mutable
import Data.Bits
import Data.DPair
import Data.Linear.Traverse1
import Data.Queue
import Data.Vect

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Token
import IO.Async.Loop.TimerST
import IO.Async.Signal

import public IO.Async
import public IO.Async.Loop
import public IO.Async.Epoll
import public IO.Async.Loop.TimerH
import public IO.Async.Loop.SignalH

import System
import System.Linux.Epoll.Prim
import System.Linux.Signalfd.Prim
import System.Linux.Timerfd.Prim
import System.Posix.Errno.IO
import System.Posix.File.Prim
import System.Posix.Limits

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

dieOnErr : EPrim a -> IO1 a
dieOnErr act t =
  case act t of
    R r t => r # t
    E x t => ioToF1 (die "Error: \{errorText x} (\{errorName x})") t

public export
0 FileHandle : Type
FileHandle = Event -> IO1 ()

hdummy : FileHandle
hdummy = \_ => dummy

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

  ||| Maximum number of files that can be opened (based
  ||| on reading the corresponding system limit at
  ||| startup)
  maxFiles : Nat

  ||| File event handles. This are invoked after receiving
  ||| events from `epoll`
  handles  : IOArray maxFiles FileHandle

  ||| C array used to store file events during polling.
  events   : CArrayIO maxFiles SEpollEvent

  ||| The `epoll` file descriptor used for polling
  epoll    : Epollfd

  ||| Remaining number of stealers. To reduce contention,
  ||| not all idle workers will be allowed to steal work
  ||| at the same time
  stealers : IORef Nat

  ||| State for schedule actions
  timer : Timer

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
    let alive   # t := refIO Run t
        ceded   # t := refIO Nothing t
        handles # t := arrayIO maxFiles hdummy t
        events  # t := ioToF1 (malloc SEpollEvent maxFiles) t
        epoll   # t := dieOnErr (epollCreate 0) t
        tim     # t := TimerST.timer t
     in W n me alive ceded queues maxFiles handles events epoll stealers tim # t

--------------------------------------------------------------------------------
-- Work Loop
--------------------------------------------------------------------------------

nextFin : {n : _} -> Fin n -> Fin n
nextFin FZ     = last
nextFin (FS x) = weaken x

%inline
elog : String -> IO1 ()
elog s = (() #) -- toF1 (File.Prim.stdoutLn s)

parameters (s : EpollST)

  %inline
  getHandle : Fd -> IO1 FileHandle
  getHandle f t =
    case tryNatToFin (cast f.fd) of
      Just v  => AC.get s.handles v t
      Nothing => hdummy # t

  handleEvs : List EpollEvent -> IO1 Nat
  handleEvs []            t = POLL_ITER # t
  handleEvs (E ev fd::es) t =
    let h # t := getHandle fd t
        _ # t := h ev t
     in  handleEvs es t

  -- Uses `epoll` to poll for file events. As long as we have
  -- other work to do, `timeout` will be 0, and this funtion will only
  -- be invoked after every `POLL_ITER` iteration of the work loop.
  --
  -- If we go to sleep, `timeout` will be set to 1 ms.
  %inline
  poll : Int32 -> IO1 Nat
  poll timeout t =
    let vs # t := dieOnErr (epollWaitVals s.epoll s.events timeout) t
     in handleEvs vs t

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
        0   => let n # t := poll 0 t in loop n t
        S k =>
         let _ # t := runDueTimers s.timer t
          in case next t of
               Just tsk # t => let _ # t := tsk.act t in loop k t
               Nothing  # t =>
                let n # t := poll 1 t
                 in loop n t

release : EpollST -> IO ()
release s = do
  free s.events
  fromPrim (close' s.epoll)

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

parameters (s         : EpollST)
           (fd        : Fd)
           (ev        : Event)
           (autoClose : Bool)
           (cb        : Either Errno Event -> IO1 ())

  -- calls `epoll_ctl` via the FFI to handle the file descriptor
  %inline
  ctl  : EpollOp -> EPrim ()
  ctl op = epollCtl s.epoll op fd ev

  -- close the file descriptor if `autoClose` is set to `True`
  -- this must be done *after* invoking `cb`.
  %inline
  closefd : IO1 ()
  closefd = when1 autoClose (toF1 $ close' fd)

  -- resets the file handle to `hdummy` and removes `fd` from the epoll set
  %inline
  cleanup : Fin s.maxFiles -> IO1 ()
  cleanup v t =
    let _ # t := AC.set s.handles v hdummy t
     in io1 (ctl Del) t

  -- invokes `cleanup` before running the file handle, and closes
  -- the file descriptor in case `autoClose` is set to `True`.
  %inline
  act : Fin s.maxFiles -> FileHandle
  act v e t =
    let _ # t := Epoll.cleanup v t
        _ # t := cb (Right e) t
     in closefd t

  -- we got a result before the file handle was registered.
  -- we invoke the callback and close the file returning a
  -- dummy cleanup hook
  %inline
  abrt : Either Errno Event -> IO1 (IO1 ())
  abrt res t =
    let _ # t := cb res t
        _ # t := closefd t
     in dummy # t

  -- cancelation hook: like `act` but without invoking the callback
  %inline
  cncl : Fin s.maxFiles -> FileHandle
  cncl v e t =
    let _ # t := Epoll.cleanup v t
     in closefd t

  pollFile : IO1 (IO1 ())
  pollFile t =
    -- tries to convert the file descriptor to an index into the array
    -- of file descriptors
    case tryNatToFin (cast fd.fd) of
      -- now trying to register the file descriptor at epoll
      Just v  => case ctl Add t of
        -- oops, this failed
        E x t => case x == EPERM of
          -- not a pollable file descriptor. we just invoke the callback with the
          -- given `Event`. this allows us to use the event loop even with
          -- regular files, giving us a single interface for asynchronous
          -- reading and writing of files
          True  => abrt (Right ev) t

          -- there was another event. pass it to the callback
          False => abrt (Left x) t

        -- success! We now register an event handler to be invoked
        -- once an epoll event is ready. care must be taken to only cleanup
        -- stuff once, lest we cleanup a new file descriptor while this one
        -- has been closed in the meantime
        R _ t   =>
         let -- atomic boolean flag indicating if the handle is still active
             -- this will be atomically set to `False` (using `once`)
             -- before running or canceling the file handle
             --
             -- `cleanup` needs to be atomic because there is a race condition
             -- between running the file handle once an event is ready and
             -- cancelation, which might happen externally and from a different
             -- thread
             r # t := refIO True t
             _ # t := AC.set s.handles v (\e => once r (act v e)) t
          in once r (cleanup v) # t
      Nothing => abrt (Left EINVAL) t

export %inline
Epoll EpollST where
  primEpoll = pollFile

export %inline
TimerH EpollST where
  primWait s dur f = schedule s.timer dur (f (Right ()))

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
  qs <- newIOArray (S k) (Queue.empty {a = Package EpollST})
  let mfs := sysconf SC_OPEN_MAX
  ss <- newIORef (half $ S k)
  ws <- workSTs (cast mfs) qs ss (S k)
  ts <- traverse (\x => fork (runIO $ loop x POLL_ITER)) (tail ws)
  let tp := TP k ts ws
  pure (tp, EL submit cede (head ws))

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
  sigprocmask SIG_BLOCK sigs
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
