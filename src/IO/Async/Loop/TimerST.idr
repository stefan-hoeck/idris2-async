module IO.Async.Loop.TimerST

import Data.SortedMap
import Data.Linear.Ref1
import Data.Linear.Traverse1
import IO.Async.Loop
import System.Clock

%default total

--------------------------------------------------------------------------------
-- Timer State
--------------------------------------------------------------------------------

record TimerST where
  constructor TST
  id  : Nat
  map : SortedMap Integer (List (Nat, IO1 ()))

schedule_ : Integer -> IO1 () -> TimerST -> TimerST
schedule_ ns act (TST id m) =
  case lookup ns m of
    Nothing => TST (S id) $ insert ns [(id,act)] m
    Just ps => TST (S id) $ insert ns ((id,act)::ps) m

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

nextDue : Integer -> IORef TimerST -> IO1 (Either Integer (List (Nat,IO1 ())))
nextDue ns r t =
  let (TST id m) # t := read1 r t
   in case leftMost m of
        Nothing       => Left 0 # t
        Just (due,ps) => case ns >= due of
          True  =>
           let _ # t := write1 r (TST id $ delete due m) t
            in Right ps # t
          False => Left (due - ns) # t

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
record Timer where
  constructor T
  ref : IORef TimerST

export
timer : IO1 Timer
timer t = let st # t := ref1 (TST 0 empty) t in T st # t

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
          True  => let _ # t := act t in unit1 # t
          False =>
            let tst # t := read1 ti.ref t
                _   # t := write1 ti.ref (schedule_ end act tst) t
             in mod1 ti.ref (drop_ end tst.id) # t

  export
  runDue : Integer -> IO1 Integer
  runDue now t =
    case nextDue now ti.ref t of
      Right ps # t =>
       let _ # t := traverse1_ snd ps t
        in runDue (assert_smaller now now) t
      Left rem # t => rem # t

  ||| Runs all scheduled timers whose duration has exceeded
  export
  runDueTimers : IO1 Integer
  runDueTimers t =
    let st # t := read1 ti.ref t
     in case leftMost st.map of
          Nothing      => 0 # t
          Just (ns,ps) =>
            let now # t := nanos t
             in case now >= ns of
                  False => (ns - now) # t
                  True  => runDue now t
