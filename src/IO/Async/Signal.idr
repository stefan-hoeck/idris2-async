module IO.Async.Signal

import IO.Async.Outcome
import IO.Async.Type
import IO.Async.Loop.SignalH
import IO.Async.Util

%default total

%foreign "scheme,chez:(lambda (s,h) (register-signal-handler s h))"
prim__registerSignalHandler : Bits32 -> (Bits32 -> PrimIO ()) -> PrimIO ()

export %inline
awaitSignal : SignalH e => Signal -> Async e es ()
awaitSignal s = do
  ev <- env
  primAsync $ \cb => primOnSignal ev s (cb $ Right ())

export %inline
onSignal : SignalH e => Signal -> Async e es a -> Async e es a
onSignal s act = awaitSignal s >> act
