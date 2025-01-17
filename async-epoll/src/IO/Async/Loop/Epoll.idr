module IO.Async.Loop.Epoll

import public Data.Nat
import Data.Array.Core as AC
import Data.Array.Mutable
import Data.Bits
import Data.Linear.Traverse1
import Data.Queue
import Data.Vect

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Token

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

setHandle : EpollST -> Fd -> FileHandle -> IO1 ()
setHandle s f fh t =
  case tryNatToFin (cast f.fd) of
    Just v  => AC.set s.handles v fh t
    Nothing => () # t

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
  let _  # t := logTimeout timeout t
      vs # t := dieOnErr (epollWaitVals s.epoll s.events timeout) t
      _  # t := logEvs vs t
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

%inline
ctl  : EpollST -> EpollOp -> Fd -> Event -> EPrim ()
ctl s op fd ev = epollCtl s.epoll op fd ev

closeIf : Fd -> Bool -> IO1 ()
closeIf fd True  t = toF1 (close' fd) t
closeIf fd False t = () # t

removeHandle : EpollST -> Fd -> Bool -> IO1 ()
removeHandle s fd autoClose t =
  case ctl s Del fd 0 t of
    R _ t => closeIf fd autoClose t
    E _ t => closeIf fd autoClose t

pollFile :
     EpollST
  -> Fd
  -> Event
  -> (autoClose : Bool)
  -> (Either Errno Event -> IO1 ())
  -> IO1 (Bool -> IO1 ())
pollFile s file ev ac fh t =
  let fd    := cast {to = Fd} file
      _ # t := setHandle s fd (fh . Right) t
   in case ctl s Add fd ev t of
        R _ t => const (removeHandle s fd ac) # t
        E x t => case x == EPERM of
          True =>
            let _ # t := fh (Right ev) t
             in const (closeIf fd ac) # t
          False =>
            let _ # t := fh (Left x) t
             in const (closeIf fd ac) # t

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
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> IO (ThreadPool, EventLoop EpollST)
mkThreadPool (S k) = do
  qs <- newIOArray (S k) (Queue.empty {a = Package EpollST})
  let mfs := sysconf SC_OPEN_MAX
  ws <- workSTs (cast mfs) qs (S k)
  ts <- traverse (\x => fork (runIO $ steal x x.me x.size)) (tail ws)
  let tp := TP k ts ws
  pure (tp, EL submit cede (head ws))

export covering
app :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> List Signal
  -> Async EpollST [] ()
  -> IO ()
app n sigs act = do
  sigprocmask SIG_BLOCK sigs
  (tp,el) <- mkThreadPool n
  tg <- newTokenGen
  runAsyncWith 1024 el act (\_ => putStrLn "Done. Shutting down" >> stop tp)
  let wst := head tp.workers
  runIO $ steal wst wst.me wst.size
  traverse_ (\x => threadWait x) tp.ids
  traverse_ release tp.workers
  usleep 100
