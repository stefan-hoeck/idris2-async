module IO.Async.Loop.SignalH

import public IO.Async.Loop
import public System.Signal

%default total

public export
interface SignalH a where
  primOnSignals : a -> List Signal -> (Signal -> IO1 ()) -> IO1 (IO1 ())
