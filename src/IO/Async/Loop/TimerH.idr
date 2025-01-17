module IO.Async.Loop.TimerH

import public IO.Async.Loop
import public System.Clock
import public System.Posix.Errno

%default total

public export
interface TimerH a where
  primWaitTill :
       a
    -> Clock Monotonic
    -> (Either Errno () -> IO1 ())
    -> IO1 (Bool -> IO1 ())
