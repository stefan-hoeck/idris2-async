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

-- State of a physical worker thread in a thread-pool.
export
record EpollST where
  constructor W
  size     : Nat
  me       : Fin size
  alive    : IORef Alive
  empty    : IORef Bool
  queues   : IOArray size (Queue $ Package EpollST)
  maxFiles : Nat
  handles  : IOArray maxFiles FileHandle
  events   : CArrayIO maxFiles SEpollEvent
  epoll    : Epollfd

public export
0 Task : Type
Task = Package EpollST

getHandle : EpollST -> Fd -> IO1 FileHandle
getHandle s f t =
  case tryNatToFin (cast f.fd) of
    Just v  => AC.get s.handles v t
    Nothing => hdummy # t

-- initialize the state of a worker thread.
workST :
     {n : Nat}
  -> Fin n
  -> (maxFiles : Nat)
  -> IOArray n (Queue Task)
  -> IO EpollST
workST me maxFiles queues =
  runIO $ \t =>
    let empty   # t := refIO True t
        alive   # t := refIO Run t
        handles # t := arrayIO maxFiles hdummy t
        events  # t := ioToF1 (malloc SEpollEvent maxFiles) t
        epoll   # t := dieOnErr (epollCreate 0) t
     in W n me alive empty queues maxFiles handles events epoll # t

release : EpollST -> IO ()
release s = do
  free s.events
  fromPrim (close' s.epoll)

next : {n : _} -> Fin n -> Fin n
next FZ     = last
next (FS x) = weaken x

covering
steal : (s : EpollST) -> Fin s.size -> Nat -> IO1 ()

logTimeout : Int32 -> IO1 ()
logTimeout 0 t = () # t
logTimeout n t = toF1 (stdoutLn "sleeping for \{show n} ms") t

logEvs : List EpollEvent -> IO1 ()
logEvs es t =
  case length es < 2 of
    True => () # t
    False => toF1 (stdoutLn "got \{show $ length es} epoll events") t

covering
poll : (s : EpollST) -> Int32 -> IO1 ()
poll s timeout t =
  let vs # t := dieOnErr (epollWaitVals s.epoll s.events timeout) t
   in go vs t

  where
    go : List EpollEvent -> IO1 ()
    go []            t = () # t
    go (E ev fd::es) t =
      let h # t := getHandle s fd t
          _ # t := h ev t
       in  go es t

covering %inline
cont : EpollST -> Package EpollST -> IO1 ()
cont s pkg t =
  let _ # t := write1 pkg.env s t
      _ # t := pkg.act t
   in poll s 0 t

covering
loop : EpollST -> Package EpollST -> IO1 ()
loop s pkg t =
  let Run # t := read1 s.alive t | _ # t => () # t
      _   # t := cont s pkg t
   in steal s s.me s.size t

steal s x 0     t =
  let _   # t := poll s 1 t
      Run # t := read1 s.alive t | _ # t => () # t
   in steal s s.me s.size t
steal s x (S k) t =
  case deqAt s.queues x t of
    Nothing  # t => steal s (next x) k t
    Just pkg # t => loop s pkg t

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

||| Sets the `stopped` flag of all worker threads and awaits
||| their termination.
stop : ThreadPool -> IO ()
stop tp = runIO $ traverse1_ (\w => write1 w.alive Stop) tp.workers

||| Submit a new `IO` action to be processed by the worker threads
||| in a thread pool.
submit : Package EpollST -> IO1 ()
submit p t =
  let st # t := read1 p.env t
   in enqAt st.queues st.me p t

covering
cede : Package EpollST -> IO1 ()
cede p t =
  let st # t := read1 p.env t
   in case deqAt st.queues st.me t of
        Nothing  # t => cont st p t
        Just pkg # t =>
          let _ # t := enqAt st.queues st.me p t
           in cont st pkg t

workSTs :
     {n : _}
  -> (maxFiles : Nat)
  -> IOArray n (Queue $ Package EpollST)
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> IO (Vect k EpollST)
workSTs maxFiles qs 0     = pure []
workSTs maxFiles qs (S k) = do
  w  <- workST (natToFinLT k) maxFiles qs
  ws <- workSTs maxFiles qs k
  pure (w::ws)

||| Create a new thread pool of `n` worker threads and additional
covering
mkThreadPool :
     (n : Subset Nat IsSucc)
  -> IO (ThreadPool, EventLoop EpollST)
mkThreadPool (Element (S k) _) = do
  qs <- newIOArray (S k) (Queue.empty {a = Package EpollST})
  let mfs := sysconf SC_OPEN_MAX
  ws <- workSTs (cast mfs) qs (S k)
  ts <- traverse (\x => fork (runIO $ steal x x.me x.size)) (tail ws)
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
  let wst := head tp.workers
  runIO $ steal wst wst.me wst.size
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
