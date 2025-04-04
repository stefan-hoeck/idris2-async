module IO.Async.Loop.SignalST

import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.SortedMap
import IO.Async.Loop
import System.Posix.Signal.Prim

%default total

0 SigMap : Type
SigMap = SortedMap Signal (List (Nat, Siginfo -> IO1 ())) 

record SignalST where
  constructor SST
  id  : Nat
  map : SigMap


await_ : IORef SignalST -> List Signal -> (Siginfo -> IO1 ()) -> IO1 Nat
await_ r sigs act t = 
  let SST id m # t := read1 r t
      _        # t := write1 r (SST (S id) (go id sigs m)) t
   in id # t
  where
    go : Nat -> List Signal -> SigMap -> SigMap
    go id []     m = m
    go id (s::ss) m =
      case lookup s m of
        Nothing => go id ss $ insert s [(id,act)] m
        Just ps => go id ss $ insert s ((id,act)::ps) m

drop_ : List Signal -> Nat -> SignalST -> SignalST
drop_ []      x st         = st
drop_ (s::ss) x (SST id m) =
  case lookup s m of
    Nothing => drop_ ss x (SST id m)
    Just vs => case filter ((x /=) . fst) vs of
      [] => drop_ ss x $ (SST id $ delete s m)
      ws => drop_ ss x $ (SST id $ insert s ws m)

dropRef : IORef SignalST -> List Signal -> Nat -> IO1 ()
dropRef r ss n t = let st # t := read1 r t in write1 r (drop_ ss n st) t

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
  let st # t := ref1 (SST 0 empty) t
   in S st # t

parameters (si : Sighandler)

  ||| Await a signal and carry out the given action once it is
  ||| fired.
  |||
  ||| This returns an action for cancelling the signal handler
  export
  await : List Signal -> (Siginfo -> IO1 ()) -> IO1 (IO1 ())
  await sigs act t =
    let ix # t := await_ si.ref sigs act t
     in dropRef si.ref sigs ix # t

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
              ss => case sigwaitinfo {es = [Errno]} ss t of
                E _   t => () # t
                R inf t => case lookup inf.signal st.map of
                  Nothing => () # t
                  Just hs =>
                    let _ # t := write1 si.ref ({map $= delete inf.signal} st) t
                     in traverse1_ (\h => snd h inf) hs t 
