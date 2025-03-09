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

import IO.Async.Internal.Ref
import IO.Async.Loop.Poller
import IO.Async.Loop.SignalST
import IO.Async.Loop.TimerST
import IO.Async.Loop.Posix
import IO.Async.Signal

import public IO.Async
import public IO.Async.Loop
import public IO.Async.Loop.PollH
import public IO.Async.Loop.TimerH
import public IO.Async.Loop.SignalH

import System
import System.Clock
import System.Linux.Epoll.Prim
import System.Posix.File.Prim
import System.Posix.Limits

%default total

--------------------------------------------------------------------------------
-- Epoll
--------------------------------------------------------------------------------

-- State used for file descriptor polling
record Epoll where
  constructor P
  ||| Number of file descriptors currently waiting to be
  ||| polled
  waiting  : IORef Nat

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

mkEpoll : IO1 Epoll
mkEpoll t =
  let maxfiles    := cast {to = Nat} (sysconf SC_OPEN_MAX)
      waiting # t := ref1 Z t
      handles # t := marray1 maxfiles hdummy t
      events  # t := malloc1 SEpollEvent maxfiles t
      epoll   # t := dieOnErr (epollCreate 0) t
   in P waiting maxfiles handles events epoll # t

--------------------------------------------------------------------------------
-- Polling for File Events
--------------------------------------------------------------------------------

parameters (p : Epoll)

  %inline
  getHandle : Fd -> IO1 FileHandle
  getHandle f t =
    case tryNatToFin (cast f.fd) of
      Just v  => AC.get p.handles v t
      Nothing => hdummy # t

  handleEvs : List PollPair -> IO1 ()
  handleEvs []            t = () # t
  handleEvs (PP fd ev::es) t =
    let h # t := getHandle fd t
        _ # t := h ev t
     in  handleEvs es t

  -- Uses `epoll` to poll for file events. As long as we have
  -- other work to do, `timeout` will be 0, and this funtion will only
  -- be invoked after every `POLL_ITER` iteration of the work loop.
  --
  -- If we go to sleep, `timeout` will be set to 1 ms.
  pollWaitImpl : (timeout : Clock Duration) -> IO1 ()
  pollWaitImpl to t =
    let vs # t := dieOnErr (epollPwait2Vals p.epoll p.events to []) t
     in handleEvs vs t

  pollImpl : IO1 ()
  pollImpl t =
    let S _ # t := read1 p.waiting t | _ # t => () # t
     in pollWaitImpl (makeDuration 0 0) t

  release : IO1 ()
  release t =
    let _ # t := free1 p.events t
     in toF1 (close' p.epoll) t

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

parameters (p         : Epoll)
           (fd        : Fd)
           (ev        : PollEvent)
           (autoClose : Bool)
           (cb        : Either Errno PollEvent -> IO1 ())

  -- calls `epoll_ctl` via the FFI to handle the file descriptor
  %inline
  ctl  : EpollOp -> E1 World [Errno] ()
  ctl op = epollCtl p.epoll op fd ev

  -- close the file descriptor if `autoClose` is set to `True`
  -- this must be done *after* invoking `cb`.
  %inline
  closefd : IO1 ()
  closefd = when1 autoClose (toF1 $ close' fd)

  -- resets the file handle to `hdummy` and removes `fd` from the epoll set
  %inline
  cleanup : Fin p.maxFiles -> IO1 ()
  cleanup v t =
    let _ # t := casmod1 p.waiting pred t
        _ # t := AC.set p.handles v hdummy t
     in e1ToF1 (ctl Del) t

  -- invokes `cleanup` before running the file handle, and closes
  -- the file descriptor in case `autoClose` is set to `True`.
  %inline
  act : Fin p.maxFiles -> FileHandle
  act v e t =
    let _ # t := Epoll.cleanup v t
        _ # t := cb (Right e) t
     in closefd t

  -- we got a result before the file handle was registered.
  -- we invoke the callback and close the file returning a
  -- dummy cleanup hook
  %inline
  abrt : Either Errno PollEvent -> IO1 (IO1 ())
  abrt res t =
    let _ # t := cb res t
        _ # t := closefd t
     in unit1 # t

  -- cancelation hook: like `act` but without invoking the callback
  %inline
  cncl : Fin p.maxFiles -> FileHandle
  cncl v e t =
    let _ # t := Epoll.cleanup v t
     in closefd t

  pollFileImpl : IO1 (IO1 ())
  pollFileImpl t =
    -- tries to convert the file descriptor to an index into the array
    -- of file descriptors
    case tryNatToFin (cast fd.fd) of
      -- now trying to register the file descriptor at epoll
      Just v  => case ctl Add t of
        -- oops, this failed
        E (Here x) t => case x == EPERM of
          -- not a pollable file descriptor. we just invoke the callback with the
          -- given `PollEvent`. this allows us to use the event loop even with
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
             r # t := ref1 True t
             _ # t := AC.set p.handles v (\e => once r (act v e)) t
             _ # t := casmod1 p.waiting S t
          in once r (cleanup v) # t
      Nothing => abrt (Left EINVAL) t

||| Initialize the state of a Linux epoll poller.
export
epollPoller : IO1 Poller
epollPoller t =
  let ep # t := mkEpoll t
   in MkPoller (pollImpl ep) (pollWaitImpl ep) (release ep) (pollFileImpl ep) # t

||| Simplified version of `app`.
|||
||| We use environment variable `IDRIS2_ASYNC_THREADS` to determine the
||| number of threads to use (default: 2) and cancel the running program
||| on receiving `SIGINT`. Other signals are not supported.
export covering
epollApp : Async Poll [] () -> IO ()
epollApp prog = do
  n <- asyncThreads
  app n [SIGINT] epollPoller cprog

  where
    cprog : Async Poll [] ()
    cprog =
      race_
        [ prog
        , dropErrs {es = [Errno]} $ onSignal SIGINT (pure ())
        ]
