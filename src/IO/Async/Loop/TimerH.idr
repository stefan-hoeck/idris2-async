module IO.Async.Loop.TimerH

import public IO.Async.Loop
import public System.Clock
import public System.Posix.Errno

%default total

public export
interface TimerH a where
  primWait : a -> Clock Duration -> (Either Errno () -> IO1 ()) -> IO1 (IO1 ())
