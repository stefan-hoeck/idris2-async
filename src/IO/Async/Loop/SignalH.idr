module IO.Async.Loop.SignalH

import System.Signal

%default total

public export
interface SignalH a where
  onSignal : a -> Signal -> PrimIO () -> PrimIO (PrimIO ())
