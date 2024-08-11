module IO.Async.Loop.Sync

import Data.SortedMap
import IO.Async.Loop
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
  canceled : Ref Bool
  act      : PrimIO ()

-- run a timer if it has not been canceled yet
runTimer : Timed -> PrimIO ()
runTimer t w =
  let MkIORes False w := readRef t.canceled w | MkIORes _ w => MkIORes () w
   in t.act w

--------------------------------------------------------------------------------
-- Loop State
--------------------------------------------------------------------------------

||| State of a synchronous event loop with timers
export
record SyncST where
  constructor SST
  timers  : Ref (SortedMap (Clock Monotonic) $ List Timed)
  queue   : Ref (SnocList $ PrimIO ())
  running : Ref Bool

export
TimerH SyncST where
  primWaitTill s c act w =
    let MkIORes ref w := newRef False w
        MkIORes _   w := modRef s.timers (insertWith (++) c [T ref act]) w
     in MkIORes (writeRef ref True) w

--------------------------------------------------------------------------------
-- Loop Implementation
--------------------------------------------------------------------------------

covering
checkTimers, checkQueue : SyncST -> PrimIO ()

covering
sleep : SyncST -> Clock Duration -> PrimIO ()

-- runs the given queue of IO actions. when this is done, we run the
-- timers
covering
run : SyncST -> List (PrimIO ()) -> PrimIO ()
run s []        w = checkTimers s w
run s (x :: xs) w = let MkIORes _ w := x w in run s xs w

-- Check if there is more work in the queue. if yes, run it, otherwise abort.
-- Note: Only call this when there are no timers left!
checkQueue s w =
  let MkIORes sa w := readRef s.queue w
      MkIORes _  w := writeRef s.queue [<] w
   in case sa <>> [] of
        [] => MkIORes () w
        as => run s as w

-- Check if we have any timers that are due and run them
checkTimers s w =
  let MkIORes ts w  := readRef s.timers w
      Just (c,ts)   := leftMost ts | Nothing => checkQueue s w
      MkIORes ts2 w := nonCanceled canceled ts w
   in case ts2 of
        [] => -- all timers have been canceled. remove them and check for more
          let MkIORes _ w := modRef s.timers (delete c) w
           in checkTimers s w
        _  => -- we have non-canceled timers. check if they are due
          let MkIORes now w := toPrim (clockTime Monotonic) w
           in case now <= c of
                -- the timers are not yet due, so sleep if we have nothing else to do
                False => sleep s (timeDifference now c) w
                -- the timers are due. run them and check for more
                True  =>
                  let MkIORes _ w := modRef s.timers (delete c) w
                      MkIORes _ w := runAll runTimer ts2 w
                   in checkTimers s w

sleep s c w =
  let MkIORes sa w := readRef s.queue w
      MkIORes _  w := writeRef s.queue [<] w
   in case sa <>> [] of
        [] => let MkIORes _ w := doSleep c w in checkTimers s w
        as => run s as w

%inline
cedeImpl : SyncST -> PrimIO () -> PrimIO ()
cedeImpl s act = modRef s.queue (:< act)

covering
spawnImpl : SyncST -> Package (SyncST) -> PrimIO ()
spawnImpl s (Pkg env act) w =
  let MkIORes _ w     := cedeImpl s act w
      MkIORes False w := readRef s.running w | MkIORes _ w => MkIORes () w
      MkIORes _ w     := writeRef s.running True w
   in run s [] w

||| A synchronous event loop running all asynchronous computations
||| on the calling thread.
|||
||| This will block the calling thread after submitting a work package until
||| the package has been completed.
export covering
sync : IO (EventLoop SyncST)
sync = do
  st <- [| SST (fromPrim $ newRef empty) (fromPrim $ newRef [<]) (fromPrim $ newRef False) |]
  pure (EL (spawnImpl st) cedeImpl st)
