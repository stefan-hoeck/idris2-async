module IO.Async.Loop.Poller

import Data.SortedMap as SM

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref

import IO.Async
import IO.Async.Loop.SignalH
import IO.Async.Loop.TimerH

import System
import System.Linux.Epoll
import System.Linux.EventFD
import System.Linux.SignalFD
import System.Linux.TimerFD

%default total

--------------------------------------------------------------------------------
-- Tasks
--------------------------------------------------------------------------------

||| An event handler for file descriptor events
public export
record FileHandle where
  constructor FH
  ||| What to do in case of an event
  actOn : Events -> PrimIO ()

  ||| Reference for closing the file
  close : Ref (PrimIO ())

0 FileHandles : Type
FileHandles = SortedMap Bits32 FileHandle

closeHandle : Ref (PrimIO ()) -> PrimIO ()
closeHandle ref w =
  let MkIORes cl w := modify ref (primDummy,) w
   in cl w

--------------------------------------------------------------------------------
-- Poller Run Loop
--------------------------------------------------------------------------------

record PollerST where
  constructor PST
  lock    : Mutex
  wakeup  : EventFD
  handles : Ref FileHandles
  alive   : Ref Alive
  epoll   : EpollFD

getHandle : PollerST -> Bits32 -> PrimIO (Maybe FileHandle)
getHandle s f = modify s.handles $ \m => (delete f m, lookup f m)

removeFile : PollerST -> Ref (PrimIO ()) -> Bits32 -> PrimIO ()
removeFile s cl f w =
  let MkIORes _ w := epollDel s.epoll f w
   in closeHandle cl w

covering
poll : PollerST -> PrimIO ()
poll s w =
  let MkIORes Run w := withMutex s.lock (readRef s.alive) w | MkIORes _ w => MkIORes () w
      MkIORes r   w := epollWait s.epoll (-1) w
   in case r of
        NoEv    => poll s w
        Ev f es =>
          let MkIORes (Just h) w := getHandle s f w | MkIORes _ w => poll s w
              MkIORes _        w := removeFile s h.close f w
              MkIORes _        w := h.actOn es w
           in poll s w
        Err x   => primDie "Epoll error: \{show x}" w

--------------------------------------------------------------------------------
-- Poller
--------------------------------------------------------------------------------

export
record Poller where
  constructor P
  id : ThreadID
  st : PollerST

||| Stops the `Poller` by setting its `Alive` flag to `Stop`.
export
stop : Poller -> IO ()
stop p = do
  putStrLn "Stopping poller"
  fromPrim $ withMutex p.st.lock $ \w =>
    let MkIORes _ w := writeRef p.st.alive Stop w
     in writeEv p.st.wakeup 1 w
  threadWait p.id

||| Creates an asynchronous scheduler for timed tasks.
|||
||| This sets up a new event loop for processing timed tasks
||| on a single additional thread. The thread will usually wait until
||| either the next scheduled task is due or a new task is submitted
||| via `submit`.
export covering
mkPoller : IO Poller
mkPoller = do
  Right efd <- epollCreate | Left err => die "Epoll error: \{err}"
  lock      <- fromPrim mkMutex
  wakeup    <- fromPrim (eventfd 0 neutral)
  alive     <- fromPrim (newRef Run)
  handles   <- fromPrim (newRef empty)
  _         <- fromPrim (epollAdd efd wakeup EPOLLIN neutral)
  let pst := PST lock wakeup handles alive efd
  id <- fork $ fromPrim $ poll pst
  pure (P id pst)

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export
addHandle :
     {auto fd : FileDesc a}
  -> Poller
  -> (file : a)
  -> Events
  -> Epoll.Flags
  -> FileHandle
  -> PrimIO (PrimIO ())
addHandle p file es fs fh w =
  let fd          := fileDesc file
      MkIORes _ w := update p.st.handles (insert fd fh) w
      MkIORes _ w := epollAdd p.st.epoll fd es fs w
   in MkIORes (removeFile p.st fh.close fd) w

export
TimerH Poller where
  primWaitTill s cl f w =
    let MkIORes now w := toPrim (clockTime Monotonic) w
     in case now >= cl of
          True  => let MkIORes _ w := f w in MkIORes primDummy w
          False =>
            let MkIORes ft  w := timerCreate MONOTONIC neutral w
                MkIORes cls w := newRef (close ft) w
                MkIORes _   w := setTime ft (timeDifference cl now) w
             in addHandle s ft EPOLLIN neutral (FH (const f) cls) w

export
SignalH Poller where
  primOnSignal s sig f w =
    let MkIORes fs  w := signalCreate [sig] neutral w
        MkIORes cls w := newRef (close fs) w
     in addHandle s fs EPOLLIN neutral (FH (const f) cls) w
