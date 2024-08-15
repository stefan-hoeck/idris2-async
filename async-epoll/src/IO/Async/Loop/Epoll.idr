module IO.Async.Loop.Epoll

import public Data.Nat
import Data.Queue
import Data.SnocList
import Data.SortedMap as SM
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
import System.Linux.Epoll
import System.Linux.EventFD
import System.Linux.SignalFD
import System.Linux.TimerFD

%default total

trace : Lazy String -> PrimIO ()
trace s = toPrim (putStrLn s)
-- trace s = MkIORes ()


||| An event handler for file descriptor events
public export
record FileHandle where
  constructor FH
  ||| What to do in case of an event
  actOn     : Events -> PrimIO ()

  ||| If the event should be observed once only
  oneShot   : Bool

  ||| If the file descriptor should automatically be closed after
  ||| handling the event
  autoClose : Bool

||| State of a single thread of a multi-threaded epoll event loop.
export
record EpollST where
  constructor EST
  nr       : Nat
  lock     : Mutex
  spwn     : EventFD
  epoll    : EpollFD
  tasks    : Ref (SnocList $ PrimIO ())
  queue    : Ref (Queue $ Package EpollST)
  handles  : Ref (SortedMap Bits32 FileHandle)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

indices : (n : Nat) -> Vect n Nat
indices 0     = []
indices (S k) = k :: indices k

removeFile : EpollST -> Bits32 -> (autoClose : Bool) -> PrimIO ()
removeFile s f cl w =
  let MkIORes _ w := epollDel s.epoll f w
      MkIORes _ w := modRef s.handles (delete f) w
   in primWhen cl (close f) w

export
addHandle :
     {auto fd : FileDesc a}
  -> (file : a)
  -> Events
  -> Epoll.Flags
  -> FileHandle
  -> EpollST
  -> PrimIO (PrimIO ())
addHandle file es fs fh s w =
  let fd          := fileDesc file
      MkIORes _ w := epollAdd s.epoll fd es fs w
      MkIORes _ w := modRef s.handles (insert fd fh) w
   in MkIORes (removeFile s fd fh.autoClose) w

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export
TimerH EpollST where
  primWaitTill s cl f w =
    let MkIORes now w := toPrim (clockTime Monotonic) w
     in case now >= cl of
          True  => let MkIORes _ w := f w in MkIORes primDummy w
          False =>
            let MkIORes ft  w := timerCreate MONOTONIC neutral w
                MkIORes _   w := setTime ft (timeDifference cl now) w
             in addHandle ft EPOLLIN EPOLLET (FH (const f) True True) s w

export
SignalH EpollST where
  primOnSignal s sig f w =
    let MkIORes _   w := blockSignals [sig] w
        MkIORes fs  w := signalCreate [sig] neutral w
     in addHandle fs EPOLLIN EPOLLET (FH (const f) True True) s w

--------------------------------------------------------------------------------
-- Loop Implementation
--------------------------------------------------------------------------------

%inline
cedeImpl : EpollST -> PrimIO () -> PrimIO ()
cedeImpl s act w = modRef s.tasks (:< act) w

drain : EpollST -> PrimIO Bool
drain s w = let MkIORes _ w := readEv s.spwn w in MkIORes False w

transfer : EpollST -> PrimIO Bool
transfer s =
  withMutex s.lock $ \w =>
    let MkIORes (Just p) w := deq s.lock s.queue w | MkIORes _ w => drain s w
        MkIORes _ w        := trace "Thread \{show s.nr} transfering a fiber" w
        MkIORes _ w        := writeRef p.env s w
        MkIORes _ w        := cedeImpl s p.act w
     in MkIORes True w


-- Polling timeout: This is 0 in case we still have tasks in the local queue,
-- otherwise it is `infinity`.
timeout : EpollST -> PrimIO Int32
timeout s w =
  let MkIORes [<]   w := readRef s.tasks w | MkIORes _ w => MkIORes 0 w
      MkIORes False w := transfer s w      | MkIORes _ w => MkIORes 0 w
   in MkIORes (-1) w

covering
poll, runTasks : EpollST -> PrimIO ()

covering
onEvent : EpollST -> Bits32 -> Events -> Maybe FileHandle -> PrimIO ()
onEvent s f es Nothing  w =
  let MkIORes _ w := trace "Closing thread \{show s.nr}" w
   in epollClose s.epoll w
onEvent s f es (Just h) w =
  let MkIORes _ w := primWhen h.oneShot (removeFile s f h.autoClose) w
      MkIORes _ w := h.actOn es w
   in runTasks s w

-- runs the given queue of IO actions. when this is done, we run the timers
covering
run : EpollST -> List (PrimIO ()) -> PrimIO ()
run s []        w = poll s w
run s (x :: xs) w =
  let MkIORes _ w := trace "Thread \{show s.nr} processing a fiber" w
      MkIORes _ w := x w
   in run s xs w

runTasks s w =
  let MkIORes sa w := readRef s.tasks w
      MkIORes _  w := writeRef s.tasks [<] w
      MkIORes _  w := trace "Thread \{show s.nr} running \{show $ length sa} tasks" w
   in run s (sa <>> []) w

poll s w =
  let MkIORes t w := timeout s w
      MkIORes _ w := trace "Thread \{show s.nr} polling at timeout \{show t}" w
      MkIORes r w := epollWait s.epoll t w
   in case r of
        NoEv   => runTasks s w
        Ev f e =>
          let MkIORes _ w := trace "Thread \{show $ s.nr} got event for \{show f}: \{show e}" w
              MkIORes m w := readRef s.handles w
           in onEvent s f e (lookup f m) w
        Err x  =>
          let MkIORes _ w := trace "Polling error: \{x}" w
           in runTasks s w

fetch : EpollST -> Events -> PrimIO ()
fetch s es w = let MkIORes _ w := transfer s w in MkIORes () w

-- initialize the state of a worker thread.
covering
epollST : Mutex -> (cncl,spwn : EventFD) -> Ref (Queue $ Package EpollST) -> Nat -> IO EpollST
epollST lock cncl spwn queue n = do
  Right efd <- epollCreate | Left err => die "Epoll error: \{err}"
  tasks     <- fromPrim (newRef [<])
  handles   <- fromPrim (newRef empty)
  let s := EST n lock spwn efd tasks queue handles
  _         <- fromPrim $ addHandle spwn EPOLLIN EPOLLEXCLUSIVE (FH (fetch s) False False) s
  _         <- fromPrim $ epollAdd efd cncl EPOLLIN neutral
  pure s

--------------------------------------------------------------------------------
-- EventLoop Implementation
--------------------------------------------------------------------------------

spawnImpl : Mutex -> EventFD -> Ref (Queue $ Package EpollST) -> Package EpollST -> PrimIO ()
spawnImpl lock spwn q p =
  withMutex lock $ \w =>
    let MkIORes _ w := trace "Spawning a fiber" w
        MkIORes _ w := modRef q (`enqueue` p) w
        MkIORes _ w := writeEv spwn 1 w
     in trace "Enqueued the fiber" w

tearDown : {n : _} -> (spwn,cncl : EventFD) -> Vect n ThreadID -> IO ()
tearDown spwn cncl ids = do
  _ <- fromPrim $ writeEv cncl (cast n)
  for_ ids (\x => threadWait x)
  fromPrim $ close spwn
  fromPrim $ close cncl

export covering
epollLoop : (n : Nat) -> (0 p : IsSucc n) => IO (EventLoop EpollST, IO ())
epollLoop (S k) = do
  lock  <- fromPrim $ mkMutex
  spwn  <- fromPrim $ eventfd 0 EFD_NONBLOCK
  cncl  <- fromPrim $ eventfd 0 neutral
  queue <- fromPrim $ newRef empty
  sts   <- traverse (epollST lock cncl spwn queue) (indices $ S k)
  ts    <- for sts $ \s => fork (fromPrim $ poll s)
  putStrLn "Starting epoll loop on \{show $ S k} threads. Spawn FD: \{show $ fileDesc spwn}, cancel FD: \{show $ fileDesc cncl}"
  pure (EL (spawnImpl lock spwn queue) cedeImpl (head sts), tearDown spwn cncl ts)

export covering
app : (n : Nat) -> {auto 0 p : IsSucc n} -> Async EpollST [] () -> IO ()
app n act = do
  (el,close) <- epollLoop n
  m  <- primIO mkMutex
  c  <- primIO makeCondition
  tg <- newTokenGen
  runAsyncWith 1024 el act (\_ => putStrLn "Done. Shutting down" >> fromPrim (conditionBroadcast c))
  primIO $ acqMutex m
  primIO $ conditionWait c m
  close
  usleep 100
