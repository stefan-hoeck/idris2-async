module IO.Async.Event

import IO.Async
import Data.IORef
import System.Concurrency

%default total

export
record Event a where
  constructor Ev
  cb   : IORef (Maybe (a -> IO ()))
  ref  : IORef (Maybe a)
  lock : Mutex

withLock : Event a -> IO b -> IO b
withLock ev f = do
  mutexAcquire ev.lock
  v <- f
  mutexRelease ev.lock
  pure v

export
newEvent : HasIO io => io (Event a)
newEvent = [| Ev (newIORef Nothing) (newIORef Nothing) makeMutex |]

export
listen : Event a -> (a -> IO ()) -> IO ()
listen ev cb = do
  run <- withLock ev $ do
    readIORef ev.ref >>= \case
      Just v  => writeIORef ev.ref Nothing $> cb v
      Nothing => writeIORef ev.cb (Just cb) $> pure ()
  run

export
send : Event a -> b -> (b -> a) -> (a -> b -> a) -> IO ()
send ev v new acc = do
  run <- withLock ev $
    readIORef ev.cb >>= \case
      Nothing => readIORef ev.ref >>= \case
        Just x  => writeIORef ev.ref (Just $ acc x v) $> pure ()
        Nothing => writeIORef ev.ref (Just $ new v) $> pure ()
      Just cb   => writeIORef ev.cb Nothing $> cb (new v)
  run

stopListening : Event a -> IO ()
stopListening ev = withLock ev $ writeIORef ev.cb Nothing

export
onEvent : Event a -> Async es a
onEvent ev =
  cancelableAsync $ \cb =>
    listen ev (cb . Succeeded) $> liftIO (stopListening ev)

public export
0 Buffer : Type -> Type
Buffer = Event . SnocList

export %inline
buffer : Buffer a -> a -> IO ()
buffer ev v = send ev v (Lin :<) (:<)
