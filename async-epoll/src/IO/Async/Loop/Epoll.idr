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
import public IO.Async.Loop.SignalH
import public IO.Async.Loop.TimerH

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
  signals  : CArrayIO 1 SSiginfo
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
        signals # t := ioToF1 (malloc SSiginfo 1) t
        epoll   # t := dieOnErr (epollCreate 0) t
     in W n me alive empty queues maxFiles handles events signals epoll # t

release : EpollST -> IO ()
release s = do
  free s.events
  free s.signals
  fromPrim (close' s.epoll)

next : {n : _} -> Fin n -> Fin n
next FZ     = last
next (FS x) = weaken x

covering
steal : (s : EpollST) -> Fin s.size -> Nat -> IO1 ()

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

covering
loop : EpollST -> Package EpollST -> IO1 ()
loop s pkg t =
  let Run # t := read1 s.alive t | _ # t => () # t
      _   # t := write1 pkg.env s t
      _   # t := pkg.act t
      _   # t := poll s 0 t
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

%inline
removeHandle : EpollST -> Fd -> IO1 ()
removeHandle s b t =
  case ctl s Del b 0 t of
    R _ t => () # t
    E _ t => () # t

pollFile :
     {auto fd : FileDesc a}
  -> EpollST
  -> (file : a)
  -> Event
  -> FileHandle
  -> EPrim (IO1 ())
pollFile s file ev fh t =
  let fd      := cast {to = Fd} file
      _ # t := setHandle s fd fh t
      R _ t := ctl s Add fd ev t | E x t => E x t
   in R (removeHandle s fd) t

andClose : FileDesc a => a -> IO1 () -> IO1 ()
andClose fd act t =
  let _ # t := act t
   in toF1 (close' fd) t

isEPOLLIN : Event -> Bool
isEPOLLIN ev = (ev.event .&. event EPOLLIN) == event EPOLLIN

htimer : Timerfd -> (Either Errno () -> IO1 ()) -> FileHandle
htimer fd act ev t = 
  case isEPOLLIN ev of
    True  => let _ # t := toF1 (close' fd) t in act (Right ()) t
    False => let _ # t := toF1 (close' fd) t in act (Left EINVAL) t

%inline
fail : (Either Errno a -> IO1 ()) -> Errno -> IO1 (IO1 ())
fail act x t = let _ # t := act (Left x) t in dummy # t

%inline
failClose :
     {auto fd : FileDesc b}
  -> b
  -> (Either Errno a -> IO1 ())
  -> Errno -> IO1 (IO1 ())
failClose vb act x t =
  let _ # t := toF1 (close' vb) t
      _ # t := act (Left x) t
   in dummy # t

%inline
succ : (Either Errno a -> IO1 ()) -> a -> IO1 (IO1 ())
succ act x t = let _ # t := act (Right x) t in dummy # t

export
TimerH EpollST where
  primWaitTill s cl f t =
    let now # t := ioToF1 (clockTime Monotonic) t
     in case now >= cl of
          True  => succ f () t
          False =>
            let ts     := TS (duration 0 0) (timeDifference cl now)
                R fd t := timerfd CLOCK_MONOTONIC 0 t | E x t => fail f x t
                R _  t := setTime fd 0 ts t | E x t => failClose fd f x t
                R cl t := pollFile s fd EPOLLIN (htimer fd f) t | E x t => failClose fd f x t
             in andClose fd cl # t

hsignal : EpollST -> Signalfd -> (Either Errno Siginfo -> IO1 ()) -> FileHandle
hsignal s fd act ev t = 
  case isEPOLLIN ev of
    False => let _ # t := toF1 (close' fd) t in act (Left EINVAL) t
    True  => case readSignalfd fd s.signals t of
      E x t =>
        let _ # t := toF1 (close' fd) t
         in act (Left x) t
      R [si] t =>
        let _ # t := toF1 (close' fd) t
         in act (Right si) t
      R _ t =>
        let _ # t := toF1 (close' fd) t
         in act (Left EINVAL) t

export
SignalH EpollST where
  primOnSignals s sigs f t =
    let R fd t := signalfd sigs 0 t | E x t => fail f x t
        R cl t := pollFile s fd EPOLLIN (hsignal s fd f) t | E x t => failClose fd f x t
     in andClose fd cl # t

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
  ids     : Vect (S size) ThreadID
  workers : Vect (S size) EpollST

||| Sets the `stopped` flag of all worker threads and awaits
||| their termination.
stop : ThreadPool -> IO ()
stop tp = do
  runIO $ traverse1_ (\w => write1 w.alive Stop) tp.workers
  traverse_ (\x => threadWait x) tp.ids
  traverse_ release tp.workers

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
        Nothing  # t => loop st p t
        Just pkg # t =>
          let _ # t := enqAt st.queues st.me p t
           in loop st pkg t

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

||| Create a new thread pool of `n` worker threads and additional thread
||| for scheduling timed tasks.
covering
mkThreadPool :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> IO (EventLoop EpollST, IO ())
mkThreadPool (S k) = do
  qs <- newIOArray (S k) (Queue.empty {a = Package EpollST})
  let mfs := sysconf SC_OPEN_MAX
  ws <- workSTs (cast mfs) qs (S k)
  ts <- traverse (\x => fork (runIO $ steal x x.me x.size)) ws
  let tp := TP k ts ws
  pure (EL submit cede (head ws), stop tp)

export covering
app :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> List Signal
  -> Async EpollST [] ()
  -> IO ()
app n sigs act = do
  sigprocmask SIG_BLOCK sigs
  (el,close) <- mkThreadPool n
  m  <- primIO mkMutex
  c  <- primIO makeCondition
  tg <- newTokenGen
  runAsyncWith 1024 el act (\_ => putStrLn "Done. Shutting down" >> fromPrim (conditionBroadcast c))
  primIO $ acqMutex m
  primIO $ conditionWait c m
  close
  usleep 100
