module IO.Async.Loop.Epoll

import Data.Nat
import Data.Queue
import Data.SortedMap as SM
import Data.Vect

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Loop
import IO.Async.Loop.SignalH
import IO.Async.Loop.TimerH

import System
import System.Linux.Epoll
import System.Linux.EventFD
import System.Linux.SignalFD
import System.Linux.TimerFD

%default total

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
  epoll    : EpollFD
  tasks    : Ref (SnocList $ PrimIO ())
  queue    : Ref (Queue $ Package EpollST)
  handles  : Ref (SortedMap Bits32 FileHandle)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- Polling timeout: This is 0 in case we still have tasks in the local queue,
-- otherwise it is `infinity`.
timeout : EpollST -> PrimIO Int32
timeout st w =
  let MkIORes [<] w := readRef st.tasks w | MkIORes _ w => MkIORes 0 w
   in MkIORes (-1) w

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
      MkIORes _ w := update s.handles (insert fd fh) w
   in MkIORes (removeFile s fd fh.autoClose) w

--------------------------------------------------------------------------------
-- Loop Implementation
--------------------------------------------------------------------------------

%inline
cedeImpl : EpollST -> PrimIO () -> PrimIO ()
cedeImpl s act = update s.tasks (:< act)

covering
poll, runTasks : EpollST -> PrimIO ()

covering
onEvent : EpollST -> Bits32 -> Events -> Maybe FileHandle -> PrimIO ()
onEvent s f es Nothing  w = epollClose s.epoll w
onEvent s f es (Just h) w =
  let MkIORes _ w := primWhen h.oneShot (removeFile s f h.autoClose) w
      MkIORes _ w := h.actOn es w
   in poll s w

-- runs the given queue of IO actions. when this is done, we run the timers
covering
run : EpollST -> List (PrimIO ()) -> PrimIO ()
run s []        w = poll s w
run s (x :: xs) w = let MkIORes _ w := x w in run s xs w

runTasks s w =
  let MkIORes sa w := readRef s.tasks w
      MkIORes _  w := writeRef s.tasks [<] w
   in run s (sa <>> []) w

poll s w =
  let MkIORes t w := timeout s w
      MkIORes r w := epollWait s.epoll t w
   in case r of
        NoEv   => runTasks s w
        Ev f e =>
          let MkIORes m w := readRef s.handles w
           in onEvent s f e (lookup f m) w
        Err x  =>
          let MkIORes _ w := toPrim (putStrLn "Polling error: \{x}") w
           in poll s w

covering
fetch : EpollST -> EventFD -> Events -> PrimIO ()
fetch s fd es w =
  let MkIORes r w := readEv fd w
   in case r of
        Left EAGAIN => MkIORes () w
        Left err    => primDie "Event read error: \{err}" w
        Right _     =>
          let MkIORes (Just p) w := syncDeq s.queue w | MkIORes _ w => MkIORes () w
              MkIORes _        w := writeRef p.env s w
              MkIORes _        w := cedeImpl s p.act w
           in fetch s fd es w

-- initialize the state of a worker thread.
covering
epollST : (cncl,spwn : EventFD) -> Ref (Queue $ Package EpollST) -> IO EpollST
epollST cncl spwn queue = do
  Right efd <- epollCreate | Left err => die "Epoll error: \{err}"
  tasks     <- fromPrim (newRef [<])
  handles   <- fromPrim (newRef empty)
  let s := EST efd tasks queue handles
  _         <- fromPrim $ addHandle spwn EPOLLIN EPOLLET (FH (fetch s spwn) False False) s
  _         <- fromPrim $ epollAdd efd cncl EPOLLIN neutral
  pure s

--------------------------------------------------------------------------------
-- EventLoop Implementation
--------------------------------------------------------------------------------

spawnImpl : EventFD -> Ref (Queue $ Package EpollST) -> Package EpollST -> PrimIO ()
spawnImpl spwn q p w =
  let MkIORes _ w := update q (`enqueue` p) w
   in writeEv spwn 1 w

tearDown : {n : _} -> (spwn,cncl : EventFD) -> Vect n ThreadID -> IO ()
tearDown spwn cncl ids = do
  _ <- fromPrim $ writeEv cncl (cast n)
  for_ ids (\x => threadWait x)
  fromPrim $ close spwn
  fromPrim $ close cncl

export covering
epollLoop : (n : Nat) -> (0 p : IsSucc n) => IO (EventLoop EpollST, IO ())
epollLoop (S k) = do
  spwn  <- fromPrim $ eventfd 0 (EFD_SEMAPHORE <+> EFD_NONBLOCK)
  cncl  <- fromPrim $ eventfd 0 neutral
  queue <- fromPrim $ newRef empty
  sts   <- sequence $ Vect.replicate (S k) (epollST cncl spwn queue)
  ts    <- for sts $ \s => fork (fromPrim $ poll s)
  pure (EL (spawnImpl spwn queue) cedeImpl (head sts), tearDown spwn cncl ts)
