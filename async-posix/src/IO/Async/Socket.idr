module IO.Async.Socket

import public IO.Async.Posix
import public System.Posix.Socket

%default total

parameters {auto has : Has Errno es}
           {auto ep  : PollH e}

  ||| Creates a new endpoint for communication returning a file descriptor
  ||| referring to that endpoint.
  |||
  ||| Unlike `System.Posix.Socket`, this will open the socket in
  ||| non-blocking mode (with the `O_NONBLOCK` flag set)
  export %inline
  socketnb : (d : Domain) -> SockType -> Async e es (Socket d)
  socketnb d t = do
    sock <- socket d t
    addFlags sock O_NONBLOCK
    pure sock

  ||| Listens on the given socket for incoming connections without blocking.
  export
  acceptnb : Socket d -> Async e es (Socket d)
  acceptnb sock = do
    assert_total $ attempt (accept {es = [Errno]} sock) >>= \case
      Right peer    => pure peer
      Left (Here x) =>
        if x == EINPROGRESS || x == EAGAIN
           then ignore (poll sock POLLOUT) >> acceptnb sock
           else throw x

  ||| Connects a socket to the given address.
  export
  connectnb : {d : _} -> Socket d -> Addr d -> Async e es ()
  connectnb sock addr =
    attempt (connect {es = [Errno]} sock addr) >>= \case
      Left (Here x) =>
        if x == EINPROGRESS || x == EAGAIN
           then ignore $ poll sock POLLOUT
           else throw x
      Right ()      => pure ()

  ||| Reads at most `n` bytes from a socket.
  export %inline
  recvnb :
       Socket d
    -> (0 r : Type)
    -> {auto frb : FromBuf r}
    -> (n : Bits32)
    -> SockFlags
    -> Async e es (ReadRes r)
  recvnb sock r n fs = do
    _ <- poll sock POLLIN
    recv sock r n fs
