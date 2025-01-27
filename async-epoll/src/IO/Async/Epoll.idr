module IO.Async.Epoll

import IO.Async.Internal.Loop
import IO.Async.Loop.SignalH
import IO.Async.Loop.TimerH
import System.Posix.File.Prim

import public IO.Async
import public IO.Async.Loop
import public IO.Async.Posix
import public System.Linux.Epoll

%default total

public export
interface Epoll a where
  primEpoll :
       a
    -> Fd
    -> Event
    -> (autoClose : Bool)
    -> (Either Errno Event -> IO1 ())
    -> IO1 (IO1 ())

parameters {auto has : Has Errno es}
           {auto ep  : Epoll e}
           {auto fd  : FileDesc f}
           (fd       : f)

  ||| Polls the file descriptor for the given events without blocking
  ||| an operating system thread.
  |||
  ||| If the file descriptor does not support polling, for instance,
  ||| because it is a regular file, this will immediately return
  ||| `ev`.
  export
  epoll : (ev : Event) -> Async e es Event
  epoll ev = do
    st <- env
    primAsync $ \cb => primEpoll st (cast fd) ev False $ \case
      Right x => cb (Right x)
      Left  x => cb (Left $ inject x)

  ||| Runs a computation after polling a file descriptor.
  |||
  ||| This allows us to read from or write to a file descriptor
  ||| without blocking an operating system thread.
  export
  onEvent : Event -> Async e es a -> Async e es a
  onEvent ev act = do
    evt <- epoll ev
    case hasEvent evt ev of
      True  => act
      False => throw EINVAL

  ||| Reads from a file descriptor without blocking.
  |||
  ||| The descriptor is polled before reading, so the read is
  ||| guaranteed to not block. Use this for reading from potentially
  ||| blocking pipes and sockets.
  export
  readnb : (0 r : Type) -> FromBuf r => Bits32 -> Async e es r
  readnb r n = onEvent EPOLLIN (read fd r n)

  ||| Writes to a file descriptor without blocking.
  |||
  ||| The descriptor is polled before writing, so the write is
  ||| guaranteed to not block. Use this for writing to potentially
  ||| blocking pipes and sockets.
  export
  writenb : ToBuf r => r -> Async e es Bits32
  writenb v = onEvent EPOLLOUT (write fd v)

  ||| Iteratively writes a value to a file descriptor making sure
  ||| that the whole value is written. Use this, if a single call to
  ||| `write` might not write the complete data (for instance, when
  ||| writing to a pipe or socket).
  |||
  |||
  export
  fwritenb : ToBuf r => r -> Async e es ()
  fwritenb v =
    case (unsafeToBuf v) of
      Left  (CP sz p) => goPtr p sz
      Right bs        => go bs

    where
      goPtr : AnyPtr -> Bits32 -> Async e es ()
      goPtr p 0  = pure ()
      goPtr p sz = do
        m <- writenb (CP sz p)
        goPtr (prim__inc_ptr p m 1) (assert_smaller sz $ sz - m)

      go : ByteString -> Async e es ()
      go (BS 0 _) = pure ()
      go bs       = do
        m <- writenb bs
        go (assert_smaller bs $ drop (cast m) bs)

  ||| Continously reads and transforms data from a file
  ||| descriptor without blocking.
  export covering
  stream :
       (0 r : Type)
    -> {auto frp : FromBuf r}
    -> Bits32
    -> (r -> Async e es ())
    -> Async e es ()
  stream r buf act =
    onEvent EPOLLIN (read fd Buf buf) >>= \case
      B 0 _ => pure ()
      b     => do
        v <- runIO (fromBuf b)
        act v
        stream r buf act

  ||| Continously reads and transforms data from a file
  ||| descriptor without blocking by loading data into a
  ||| preallocated pointer.
  |||
  ||| For very large files, this can be faster than `stream` if
  ||| the data in question can be transformed in place without allocating
  ||| additional memory. This also allows us to use a very large buffer
  ||| even in case we often only read small amounts of data.
  export covering
  streamp :
       (0 r : Type)
    -> {auto frp : FromPtr r}
    -> CPtr
    -> (r -> Async e es ())
    -> Async e es ()
  streamp r cp act =
    onEvent EPOLLIN (readPtr fd CPtr cp) >>= \case
      CP 0 _ => pure ()
      cp2    => do
        v <- runIO (fromPtr cp2)
        act v
        streamp r cp act
