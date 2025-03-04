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
  |||
  |||
  export
  acceptnb : Socket d -> Async e es (Maybe $ Socket d)
  acceptnb sock = do
    ev <- poll sock POLLIN
    case hasEvent POLLIN ev of
      False => pure Nothing
      True  => ifError EAGAIN Nothing $ do
        peer <- accept sock
        addFlags peer O_NONBLOCK
        pure (Just peer)

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
