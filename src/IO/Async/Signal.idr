module IO.Async.Signal

import IO.Async.Outcome
import IO.Async.Type
import IO.Async.Loop.SignalH
import IO.Async.Util

%default total

export %inline
awaitSignals : SignalH e => List Signal -> Async e es Signal
awaitSignals s = do
  ev <- env
  primAsync $ \cb => primOnSignals ev s (cb . Right)

export %inline
onSignals : SignalH e => List Signal -> Async e es a -> Async e es a
onSignals s act = ignore (awaitSignals s) >> act

export %inline
onSignal : SignalH e => Signal -> Async e es a -> Async e es a
onSignal = onSignals . pure
