module IO.Async.Loop.Sync

import Data.SortedMap
import public IO.Async.Loop
import IO.Async.Loop.TimerH
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import System.Clock

%default total

--------------------------------------------------------------------------------
-- Timed Computations
--------------------------------------------------------------------------------

record Timed where
  constructor T
  canceled : IORef Bool
  act      : IO1 ()

-- run a timer if it has not been canceled yet
runTimer : Timed -> IO1 ()
runTimer tm t =
  let False # t := read1 tm.canceled t | _ # t => () # t
   in tm.act t

--------------------------------------------------------------------------------
-- Loop State
--------------------------------------------------------------------------------

||| State of a synchronous event loop with timers
export
record SyncST where
  constructor SST
  timers  : IORef (SortedMap (Clock Monotonic) $ List Timed)
  queue   : IORef (SnocList $ IO1 ())
  running : IORef Bool

export
TimerH SyncST where
  primWaitTill s c act t =
    let ref # t := refIO False t
        _   # t := mod1 s.timers (insertWith (++) c [T ref act]) t
     in (write1 ref True) # t

--------------------------------------------------------------------------------
-- Loop Implementation
--------------------------------------------------------------------------------

covering
checkTimers, checkQueue : SyncST -> IO1 ()

covering
sleep : SyncST -> Clock Duration -> IO1 ()

-- runs the given queue of IO actions. when this is done, we run the
-- timers
covering
run : SyncST -> List (IO1 ()) -> IO1 ()
run s []        t = checkTimers s t
run s (x :: xs) t = let _ # t := x t in run s xs t

-- Check if there is more work in the queue. if yes, run it, otherwise abort.
-- Note: Only call this when there are no timers left!
checkQueue s t =
  let sa # t := read1 s.queue t
      _  # t := write1 s.queue [<] t
   in case sa <>> [] of
        [] => () # t
        as => run s as t

-- Check if we have any timers that are due and run them
checkTimers s t =
  let ts # t      := read1 s.timers t
      Just (c,ts) := leftMost ts | Nothing => checkQueue s t
   in case nonCanceled canceled ts t of
        []  # t => -- all timers have been canceled. remove them and check for more
          let _ # t := mod1 s.timers (delete c) t
           in checkTimers s t
        ts2 # t => -- we have non-canceled timers. check if they are due
          let now # t := ioToF1 (clockTime Monotonic) t
           in case now <= c of
                -- the timers are not yet due, so sleep if we have nothing else to do
                False => sleep s (timeDifference now c) t
                -- the timers are due. run them and check for more
                True  =>
                  let _ # t := mod1 s.timers (delete c) t
                      _ # t := runAll runTimer ts2 t
                   in checkTimers s t

sleep s c t =
  let sa # t := read1 s.queue t
      _  # t := write1 s.queue [<] t
   in case sa <>> [] of
        [] => let _ # t := doSleep c t in checkTimers s t
        as => run s as t

%inline
cedeImpl : Package SyncST -> IO1 ()
cedeImpl (Pkg env act) t =
  let s # t := read1 env t
   in mod1 s.queue (:< act) t

covering
spawnImpl : Package (SyncST) -> IO1 ()
spawnImpl pkg t =
  let _     # t := cedeImpl pkg t
      s     # t := read1 pkg.env t
      False # t := read1 s.running t | _ # t => () # t
      _     # t := write1 s.running True t
   in run s [] t

||| A synchronous event loop running all asynchronous computations
||| on the calling thread.
|||
||| This will block the calling thread after submitting a work package until
||| the package has been completed.
export covering
sync : IO (EventLoop SyncST)
sync = do
  st <- [| SST (newIORef empty) (newIORef [<]) (newIORef False) |]
  pure (EL spawnImpl cedeImpl st)
