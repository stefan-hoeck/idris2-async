module IO.Async.Loop.TimerH

import System.Clock

%default total

public export
interface TimerH a where
  primWaitTill : a -> Clock Monotonic -> PrimIO () -> PrimIO (PrimIO ())
