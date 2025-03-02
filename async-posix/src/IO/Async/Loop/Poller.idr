||| Posix-compliant file polling based on the `poll` system call.
|||
||| This form of file polling takes linear time with relation for
||| the number of file descriptors to be polled, which is perfectly
||| fine for polling small numbers of file descriptors. For polling
||| hundreds or thousands of file descriptors, consider using
||| the poller from async-epoll, which is based on the Linux-only
||| `epoll` system calls.
module IO.Async.Loop.Poller

import Data.Linear.Ref1
import Data.SortedMap

import IO.Async.Internal.Ref

import System
import System.Clock
import System.Posix.File.Prim
import System.Posix.Poll.Prim

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export
dieOnErr : E1 World [Errno] a -> IO1 a
dieOnErr act t =
  case act t of
    R r        t => r # t
    E (Here x) t => ioToF1 (die "Error: \{errorText x} (\{errorName x})") t

public export
0 FileHandle : Type
FileHandle = PollEvent -> IO1 ()

export
hdummy : FileHandle
hdummy = \_ => unit1

--------------------------------------------------------------------------------
-- Poller
--------------------------------------------------------------------------------

public export
record Poller where
  constructor MkPoller
  poll     : IO1 ()
  pollWait : Clock Duration -> IO1 ()
  release  : IO1 ()
  pollFile :
       (fd        : Fd)
    -> (ev        : PollEvent)
    -> (autoClose : Bool)
    -> (cb        : Either Errno PollEvent -> IO1 ())
    -> IO1 (IO1 ())

--------------------------------------------------------------------------------
-- Posix compatible polling via `poll`
--------------------------------------------------------------------------------

-- State used for file descriptor polling
record Posix where
  constructor PX
  ||| File event handles. This are invoked after receiving
  ||| events from `epoll`
  handles  : IORef (SortedMap Fd (PollEvent, FileHandle))

parameters (p : Posix)

  %inline
  getHandle : Fd -> IO1 (Maybe (PollEvent,FileHandle))
  getHandle fd t =
    let m # t := read1 p.handles t
     in lookup fd m # t

  handleEvs : List PollPair -> IO1 ()
  handleEvs []             t = () # t
  handleEvs (PP fd ev::es) t =
    let Just (_,h) # t := getHandle fd t | Nothing # t => handleEvs es t
        _ # t := h ev t
     in handleEvs es t

  -- Uses `poll` to poll for file events.
  pollWaitImpl : (timeout : Clock Duration) -> IO1 ()
  pollWaitImpl to t =
    let ms      := seconds to * 1000 + (nanoseconds to `div` 1000000)
        fds # t := read1 p.handles t
        pairs   := (\(fd,e,_) => PP fd e) <$> kvList fds
        vs # t  := dieOnErr (pollList pairs (cast ms)) t
     in handleEvs vs t

  pollImpl : IO1 ()
  pollImpl t =
    let m # t := read1 p.handles t
     in if null m then () # t else pollWaitImpl (makeDuration 0 0) t

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

parameters (p         : Posix)
           (fd        : Fd)
           (ev        : PollEvent)
           (autoClose : Bool)
           (cb        : Either Errno PollEvent -> IO1 ())

  -- close the file descriptor if `autoClose` is set to `True`
  -- this must be done *after* invoking `cb`.
  %inline
  closefd : IO1 ()
  closefd = when1 autoClose (toF1 $ close' fd)

  -- resets the file handle to `hdummy` and removes `fd` from the epoll set
  %inline
  cleanup : IO1 ()
  cleanup = mod1 p.handles (delete fd)

  -- invokes `cleanup` before running the file handle, and closes
  -- the file descriptor in case `autoClose` is set to `True`.
  %inline
  act : FileHandle
  act e t =
    let _ # t := Poller.cleanup t
        _ # t := cb (Right e) t
     in closefd t

  -- cancelation hook: like `act` but without invoking the callback
  %inline
  cncl : FileHandle
  cncl e t =
    let _ # t := Poller.cleanup t
     in closefd t

  pollFileImpl : IO1 (IO1 ())
  pollFileImpl t =
    let -- atomic boolean flag indicating if the handle is still active
        -- this will be atomically set to `False` (using `once`)
        -- before running or canceling the file handle
        --
        -- `cleanup` needs to be atomic because there is a race condition
        -- between running the file handle once an event is ready and
        -- cancelation, which might happen externally and from a different
        -- thread
        r  # t := ref1 True t
        mp # t := mod1 p.handles (insert fd (ev, \e => once r (act e))) t
     in once r cleanup # t

||| initialize the state of a posix-compatible poller.
export
posixPoller : IO1 Poller
posixPoller t =
  let ref # t := ref1 SortedMap.empty t
      px      := PX ref
   in MkPoller (pollImpl px) (pollWaitImpl px) unit1 (pollFileImpl px) # t
