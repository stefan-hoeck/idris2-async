module IO.Async.Loop.TimerST

import Data.SortedMap
import Data.Linear.Ref1
import IO.Async.Loop
import IO.Async.Internal.Loop
import System.Clock

%default total

--------------------------------------------------------------------------------
-- Timer State
--------------------------------------------------------------------------------

record TimerST where
  constructor TST
  id  : Nat
  map : SortedMap Integer (List (Nat, IO1 ()))

%inline
schedule_ : Integer -> IO1 () -> TimerST -> (TimerST, Nat)
schedule_ ns act (TST id m) =
  case lookup ns m of
    Nothing => (TST (S id) $ insert ns [(id,act)] m,     id)
    Just ps => (TST (S id) $ insert ns ((id,act)::ps) m, id)

drop_ : Integer -> Nat -> TimerST -> TimerST
drop_ ns x (TST id m) =
  case lookup ns m of
    Nothing => TST id m
    Just vs => case filter ((x /=) . fst) vs of
      [] => TST id $ delete ns m
      ws => TST id $ insert ns ws m

%inline
nanos : IO1 Integer
nanos t =
  let now # t := ioToF1 (clockTime Monotonic) t
   in toNano now # t

nextDue : Integer -> TimerST -> (TimerST, Maybe (List (Nat,IO1 ())))
nextDue ns tst@(TST id m) =
  case leftMost m of
    Nothing       => (tst, Nothing)
    Just (due,ps) => case ns >= due of
      True  => (TST id $ delete due m, Just ps)
      False => (tst, Nothing)

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
record Timer where
  constructor T
  ref : IORef TimerST

export
timer : IO1 Timer
timer t = let st # t := refIO (TST 0 empty) t in T st # t

parameters (ti : Timer)

  ||| Schedule an action at the given timer
  |||
  ||| This returns an action for cancelling the timer
  export
  schedule : Clock Duration -> IO1 () -> IO1 (IO1 ())
  schedule dur act t =
    let ns  # t := nanos t
        end     := ns + toNano dur
     in case end <= ns of
          True  => let _ # t := act t in dummy # t
          False =>
            let ix # t := casupdate1 ti.ref (schedule_ end act) t
             in casmod1 ti.ref (drop_ end ix) # t

  export
  runDue : Integer -> IO1 ()
  runDue now t =
    case casupdate1 ti.ref (nextDue now) t of
      Just ps # t =>
       let _ # t := runAll snd ps t
        in runDue (assert_smaller now now) t
      Nothing # t => () # t

  ||| Runs all scheduled timers whose duration has exceeded
  export
  runDueTimers : IO1 ()
  runDueTimers t =
    let st # t := read1 ti.ref t
     in case leftMost st.map of
          Nothing      => () # t
          Just (ns,ps) =>
            let now # t := nanos t
             in case now >= ns of
                  False => () # t
                  True  => runDue now t
