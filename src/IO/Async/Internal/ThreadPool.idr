||| A pool of a fixed number of worker threads, each operating on its own
||| work queue.
|||
||| Idle threads will try and take work packages from a shared queue, or
||| the will sleep until new work packages are available.
module IO.Async.Internal.ThreadPool

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Timer
import Data.List
import Data.Queue
import public IO.Async.Internal.ExecutionContext
import public Data.Nat

%default total

--------------------------------------------------------------------------------
-- Worker
--------------------------------------------------------------------------------

FETCH_INTERVAL : Nat
FETCH_INTERVAL = 16

-- State of a physical worker thread in a thread-pool.
record WorkST where
  constructor W
  mutex : Mutex
  cond  : Condition
  alive : Ref Alive
  timer : Timer

  -- Queue of packages this worker reads from at regular
  -- intervals or when it is otherwise idle
  outer : Ref (Queue Package)

  -- Queue of actions to be run on this thread.
  queue : Ref (Queue $ PrimIO ())

-- initialize the state of a worker thread.
workST :
     Mutex
  -> Condition
  -> Ref Alive
  -> Timer
  -> Ref (Queue Package)
  -> IO WorkST
workST m c s t p =
  fromPrim $ \w =>
    let MkIORes q w := newRef empty w
     in MkIORes (W m c s t p q) w

submitWork : WorkST -> (k : PkgKind) -> PkgType k -> PrimIO ()
submitWork s CPU      a w = enq s.queue a w
submitWork s Blocking a w = enq s.queue a w
submitWork s Timed    a w = submit s.timer a w

pkg : WorkST -> PrimIO Bool
pkg s w =
  let MkIORes (Just p) w := syncDeq s.outer w | MkIORes _ w => MkIORes False w
      MkIORes _        w := writeRef p.cont (submitWork s) w
      MkIORes _        w := enq s.queue p.act w
   in MkIORes True w

-- make sure we have nothing to do and have not been stopped, and
-- if that's the case, go to sleep
rest : WorkST -> PrimIO Work
rest s =
  withMutex s.mutex $ \w =>
    let MkIORes False w := pkg s w | MkIORes _ w => noWork w
        MkIORes Run   w := readRef s.alive w | MkIORes _ w => done w
        MkIORes _     w := conditionWait s.cond s.mutex w
        MkIORes Run   w := readRef s.alive w | MkIORes _ w => done w
        MkIORes _     w := pkg s w
     in noWork w

covering
run : WorkST -> Nat -> PrimIO ()
run s 0  w =
  let MkIORes _ w := pkg s w
   in run s FETCH_INTERVAL w

run s (S k) w =
  let MkIORes mp w := deq s.queue w
   in case mp of
        Nothing =>
          let MkIORes (W _) w := rest s w | MkIORes _ w => MkIORes () w
           in run s k w
        Just p => let MkIORes _ w := p w in run s k w

||| A fixed-size pool of `n` physical worker threads.
|||
||| Tasks are submited to the worker threads in round-robin
||| fashion: A new task is submitted to the next worker in line,
||| restarting at the beginning when reaching the last worker.
export
record ThreadPool where
  constructor TP
  ids   : List ThreadID
  lock  : Mutex
  cond  : Condition
  timer : Timer
  alive : Ref Alive
  queue : Ref (Queue Package)

||| Create a new thread pool of `n` worker threads and additional thread
||| for scheduling timed tasks.
export covering
mkThreadPool : (n : Nat) -> {auto 0 p : IsSucc n} -> IO ThreadPool
mkThreadPool n = do
  m  <- primIO mkMutex
  c  <- primIO makeCondition
  t  <- mkTimer
  s  <- primIO (newRef Run)
  q  <- primIO (newRef empty)
  ws <- sequence (replicate n $ workST m c s t q)
  ts <- traverse (\x => fork $ fromPrim $ run x 0) ws
  pure (TP ts m c t s q)

||| Sets the `stopped` flag of all worker threads and awaits
||| their termination.
export
stop : ThreadPool -> IO ()
stop tp = do
  stop tp.timer
  primIO $ withMutex tp.lock $ \w =>
    let MkIORes _ w := writeRef tp.alive Stop w
     in conditionBroadcast tp.cond w
  traverse_ (\x => threadWait x) tp.ids

||| Submit a new `IO` action to be processed by the worker threads
||| in a thread pool.
export
submit : ThreadPool -> Package -> PrimIO ()
submit tp p =
  withMutex tp.lock $ \w =>
    let MkIORes _ w := update tp.queue (`enqueue` p) w
     in conditionSignal tp.cond w

||| Create an execution context from a thread pool.
export %inline
ec : ThreadPool -> ExecutionContext
ec wp = EC (submit wp) (MkIORes ())
