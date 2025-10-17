module IO.Async.JS

import Data.Linear.Ref1
import public IO.Async
import public IO.Async.Loop
import public IO.Async.Loop.TimerH

%default total

0 Task : Type

export
record JS where
  constructor J
  ||| Reference indicating whether the queue is currently
  ||| being processed
  running  : IORef Bool

  ||| Work queue of this worker
  queue    : IORef (SnocList Task)

Task = FbrState JS

covering
spawnImpl : JS -> Task -> IO1 ()

export %inline covering
EventLoop JS where
  spawn = spawnImpl
  limit = 1024

export covering
app : Async JS [] () -> IO ()
app prog = do
  r <- newref False
  q <- newref [<]
  runAsyncWith (J r q) prog (\_ => putStrLn "Done. Shutting down")


--------------------------------------------------------------------------------
-- Timers
--------------------------------------------------------------------------------

%foreign "javascript:lambda:(m,f,w) => setTimeout(f, Number(m))"
prim__setTimeout : Integer -> PrimIO () -> PrimIO Bits32

%foreign "javascript:lambda:(i,w) => clearTimeout(i)"
prim__clearTimeout : Bits32 -> PrimIO ()

export
TimerH JS where
  primWait s cl act t =
   let ms    := toNano cl `div` 1_000_000
       x # t := ffi (prim__setTimeout ms (primRun act)) t
    in ffi (prim__clearTimeout x) # t

--------------------------------------------------------------------------------
-- Run Loop
--------------------------------------------------------------------------------

covering
checkQueue : JS -> IO1 ()

covering
run : JS -> List Task -> IO1 ()
run s []        t = checkQueue s t
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
        [] => write1 s.running False t
        as => run s as t

spawnImpl s x t =
 let True # t := read1 s.running t | False # t => run s [x] t
  in mod1 s.queue (:<x) t
