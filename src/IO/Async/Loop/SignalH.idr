module IO.Async.Loop.SignalH

import public System.Signal

%default total

public export
interface SignalH a where
  primOnSignals : a -> List Signal -> (Signal -> PrimIO ()) -> PrimIO (PrimIO ())
