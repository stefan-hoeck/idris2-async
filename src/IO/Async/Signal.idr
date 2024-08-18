module IO.Async.Signal

import IO.Async.Outcome
import IO.Async.Type
import IO.Async.Loop.SignalH
import IO.Async.Util

%default total

export %inline
awaitSignal : SignalH e => Signal -> Async e es ()
awaitSignal s = do
  ev <- env
  primAsync $ \cb => primOnSignal ev s (cb $ Right ())

export %inline
onSignal : SignalH e => Signal -> Async e es a -> Async e es a
onSignal s act = awaitSignal s >> act
