module IO.Async.Loop.SignalH

import public System.Signal

%default total

public export
interface SignalH a where
  primOnSignal : a -> Signal -> PrimIO () -> PrimIO (PrimIO ())