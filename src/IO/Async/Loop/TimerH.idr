module IO.Async.Loop.TimerH

import public IO.Async.Loop
import public System.Clock

%default total

public export
interface TimerH a where
  primWaitTill : a -> Clock Monotonic -> IO1 () -> IO1 (IO1 ())
