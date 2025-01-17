module IO.Async.Loop.SignalH

import public IO.Async.Loop
import public System.Posix.Errno
import public System.Posix.Signal

%default total

public export
interface SignalH a where
  primOnSignals :
       a
    -> List Signal
    -> (Either Errno Siginfo -> IO1 ())
    -> IO1 (Bool -> IO1 ())
