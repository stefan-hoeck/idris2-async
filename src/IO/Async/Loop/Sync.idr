module IO.Async.Loop.Sync

import Data.Linear.Traverse1
import Data.So
import Data.SortedMap
import public IO.Async.Loop
import IO.Async.Loop.TimerH
import IO.Async.Loop.TimerST
import IO.Async.Internal.Ref
import System.Clock
import System

%default total

--------------------------------------------------------------------------------
-- Loop State
--------------------------------------------------------------------------------

||| State of a synchronous event loop with timers
export
record SyncST where
  constructor SST
  timer   : Timer
  queue   : IORef (SnocList $ FbrState SyncST)
  running : IORef Bool

export %inline
TimerH SyncST where
  primWait s dur f = schedule s.timer dur f

--------------------------------------------------------------------------------
-- Loop Implementation
--------------------------------------------------------------------------------

covering
spawnImpl : SyncST -> FbrState SyncST -> IO1 ()

export %inline covering
EventLoop SyncST where
  spawn = spawnImpl
  limit = 1024

covering
checkTimers, checkQueue : SyncST -> IO1 ()

-- runs the given queue of IO actions. when this is done, we run the
-- timers
covering
run : SyncST -> List (FbrState SyncST) -> IO1 ()
run s []        t = checkTimers s t
run s (x :: xs) t =
  case runFbr s x t of
    Cont fst # t => let _ # t := mod1 s.queue (:< fst) t in run s xs t
    Done     # t => run s xs t

-- Check if there is more work in the queue. if yes, run it, otherwise abort.
-- Note: Only call this when there are no timers left!
checkQueue s t =
  let sa # t := read1 s.queue t
      _  # t := write1 s.queue [<] t
   in case sa <>> [] of
        [] => () # t
        as => run s as t

doSleep : Integer -> IO1 ()
doSleep n t =
  let v := cast {to = Int} (n `div` 1000)
   in case choose (v >= 0) of
        Left x  => ioToF1 (usleep v) t
        Right x => () # t

-- Check if we have any timers that are due and run them
checkTimers s t =
 case runDueTimers s.timer t of
   0 # t => checkQueue s t
   n # t => case read1 s.queue t of
     [<] # t => let _ # t := doSleep n t in checkTimers s t
     _   # t => checkQueue s t

spawnImpl s pkg t =
  let _     # t := mod1 s.queue (:< pkg) t
      False # t := read1 s.running t | _ # t => () # t
      _     # t := write1 s.running True t
   in run s [] t

||| A synchronous event loop running all asynchronous computations
||| on the calling thread.
|||
||| This will block the calling thread after submitting a work package until
||| the package has been completed.
export covering
sync : IO SyncST
sync = [| SST (runIO timer) (newref [<]) (newref False) |]
