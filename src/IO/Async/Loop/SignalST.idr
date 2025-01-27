module IO.Async.Loop.SignalST

import Data.Linear.Ref1
import Data.SortedMap
import IO.Async.Internal.Loop
import IO.Async.Loop
import System.Posix.Signal.Prim

%default total

0 SigMap : Type
SigMap = SortedMap Signal (List (Nat, Siginfo -> IO1 ())) 

record SignalST where
  constructor SST
  id  : Nat
  map : SigMap


await_ : List Signal -> (Siginfo -> IO1 ()) -> SignalST -> (SignalST, Nat)
await_ sigs act (SST id m) = (SST (S id) (go sigs m), id)
  where
    go : List Signal -> SigMap -> SigMap
    go []     m = m
    go (s::ss) m =
      case lookup s m of
        Nothing => go ss $ insert s [(id,act)] m
        Just ps => go ss $ insert s ((id,act)::ps) m

drop_ : List Signal -> Nat -> SignalST -> SignalST
drop_ []      x st         = st
drop_ (s::ss) x (SST id m) =
  case lookup s m of
    Nothing => drop_ ss x (SST id m)
    Just vs => case filter ((x /=) . fst) vs of
      [] => drop_ ss x $ (SST id $ delete s m)
      ws => drop_ ss x $ (SST id $ insert s ws m)

%inline
hasHandle : SignalST -> Signal -> Bool
hasHandle s sig =
  case lookup sig s.map of
    Just (_::_) => True
    _           => False

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
record Sighandler where
  constructor S
  ref  : IORef SignalST

export
sighandler : IO1 Sighandler
sighandler t =
  let st # t := refIO (SST 0 empty) t
   in S st # t

parameters (si : Sighandler)

  ||| Await a signal and carry out the given action once it is
  ||| fired.
  |||
  ||| This returns an action for cancelling the signal handler
  export
  await : List Signal -> (Siginfo -> IO1 ()) -> IO1 (IO1 ())
  await sigs act t =
    let ix # t := casupdate1 si.ref (await_ sigs act) t
     in casmod1 si.ref (drop_ sigs ix) # t

  ||| Checks for pending signals and runs the corresponding
  ||| signal handlers (if any).
  export
  checkSignals : IO1 ()
  checkSignals t =
    let st # t := read1 si.ref t
     in case null st.map of
          True  => () # t -- don't do anything if there are no signal handlers
          False => case toF1 sigpending t of -- check pending signals
            [] # t => () # t -- no pending signals. abort.
            ss # t => case filter (hasHandle st) ss of -- check handled signals
              [] => () # t -- we don't handle any pending signals. abort.
              ss => case sigwaitinfo ss t of
                E _   t => () # t
                R inf t => case lookup inf.signal st.map of
                  Nothing => () # t
                  Just hs =>
                    let _ # t := write1 si.ref ({map $= delete inf.signal} st) t
                     in runAll (\h => snd h inf) hs t 
