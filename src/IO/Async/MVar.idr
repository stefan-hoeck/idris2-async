module IO.Async.MVar

import Data.IORef
import Data.Queue
import System.Concurrency

%default total

--------------------------------------------------------------------------------
-- MVar
--------------------------------------------------------------------------------

||| A thread-safe mutable variable.
|||
||| This comes with several atomic operations: `readMVar`,
||| `writeMVar`, `modifyMVar`, and `evalState`.
|||
||| "Atomic" in this context means, that during such an operation,
||| no other thread will be able to access the mutable variable.
|||
||| This uses a `System.Concurrency.Mutex` internally, so it will only
||| be available on the Scheme backends.
export
record MVar a where
  constructor MV
  ref  : IORef a
  lock : Mutex

||| Create a new mutable variable.
export
newMVar : a -> IO (MVar a)
newMVar v = [| MV (newIORef v) makeMutex |]

withLock : MVar a -> (IORef a -> IO b) -> IO b
withLock mv f = do
  mutexAcquire mv.lock
  vb <- f mv.ref
  mutexRelease mv.lock
  pure vb

||| Atomically read the value from a mutable variable.
export %inline
readMVar : MVar a -> IO a
readMVar mv = withLock mv readIORef

||| Atomically write a value into a mutable variable.
export %inline
writeMVar : MVar a -> a -> IO ()
writeMVar mv v = withLock mv (`writeIORef` v)

||| Atomically modify the value in a mutable variable.
export %inline
modifyMVar : MVar a -> (a -> a) -> IO ()
modifyMVar mv f = withLock mv (`modifyIORef` f)

||| Atomically modify and extract the value from a
||| mutable variable.
export
evalState : MVar a -> (a -> (a,b)) -> IO b
evalState mv f =
  withLock mv $ \ref => do
    (st,res) <- f <$> readIORef ref
    writeIORef ref st
    pure res

--------------------------------------------------------------------------------
-- MQueue
--------------------------------------------------------------------------------

export
record MQueue a where
  constructor MQ
  var : MVar (Queue a)

export
newMQueue : IO (MQueue a)
newMQueue = MQ <$> newMVar empty

export
enqueue : MQueue a -> a -> IO ()
enqueue (MQ m) v = modifyMVar m (`enqueue` v)

export
dequeue : MQueue a -> IO (Maybe a)
dequeue (MQ m) =
  evalState m $ \x => case dequeue x of
    Nothing    => (x,Nothing)
    Just (v,y) => (y, Just v)
