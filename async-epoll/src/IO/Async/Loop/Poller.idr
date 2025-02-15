module IO.Async.Loop.Poller

import Data.Nat
import Data.Array.Core as AC
import Data.Array.Mutable
import Data.Linear.Traverse1

import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Loop.TimerH
import IO.Async.Loop.SignalH

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
-- Poller
--------------------------------------------------------------------------------

-- State used for file descriptor polling
public export
record Poller where
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

||| initialize the state of a worker thread.
export
poller : (maxFiles : Nat) -> IO1 Poller
poller maxFiles t =
  let waiting # t := Ref1.ref Z t
      handles # t := newMArray maxFiles hdummy t
      events  # t := ioToF1 (malloc SEpollEvent maxFiles) t
      epoll   # t := dieOnErr (epollCreate 0) t
   in P waiting maxFiles handles events epoll # t

--------------------------------------------------------------------------------
-- Polling for File Events
--------------------------------------------------------------------------------

parameters (p : Poller)

  %inline
  getHandle : Fd -> IO1 FileHandle
  getHandle f t =
    case tryNatToFin (cast f.fd) of
      Just v  => AC.get p.handles v t
      Nothing => hdummy # t

  handleEvs : List EpollEvent -> IO1 ()
  handleEvs []            t = () # t
  handleEvs (E ev fd::es) t =
    let h # t := getHandle fd t
        _ # t := h ev t
     in  handleEvs es t

  -- Uses `epoll` to poll for file events. As long as we have
  -- other work to do, `timeout` will be 0, and this funtion will only
  -- be invoked after every `POLL_ITER` iteration of the work loop.
  --
  -- If we go to sleep, `timeout` will be set to 1 ms.
  export %inline
  pollWait : (timeout : Clock Duration) -> IO1 ()
  pollWait to t =
    let vs # t := dieOnErr (epollPwait2Vals p.epoll p.events to []) t
     in handleEvs vs t

  export %inline
  poll : IO1 ()
  poll t =
    let S _ # t := read1 p.waiting t | _ # t => () # t
     in pollWait (makeDuration 0 0) t

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

parameters (p         : Poller)
           (fd        : Fd)
           (ev        : Event)
           (autoClose : Bool)
           (cb        : Either Errno Event -> IO1 ())

  -- calls `epoll_ctl` via the FFI to handle the file descriptor
  %inline
  ctl  : EpollOp -> EPrim ()
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
    let _ # t := mod1 p.waiting pred t
        _ # t := AC.set p.handles v hdummy t
     in io1 (ctl Del) t

  -- invokes `cleanup` before running the file handle, and closes
  -- the file descriptor in case `autoClose` is set to `True`.
  %inline
  act : Fin p.maxFiles -> FileHandle
  act v e t =
    let _ # t := Poller.cleanup v t
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
  cncl : Fin p.maxFiles -> FileHandle
  cncl v e t =
    let _ # t := Poller.cleanup v t
     in closefd t

  ||| Registers a file handle for polling
  export
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
             r # t := Ref1.ref True t
             _ # t := AC.set p.handles v (\e => once r (act v e)) t
             _ # t := mod1 p.waiting S t
          in once r (cleanup v) # t
      Nothing => abrt (Left EINVAL) t
