module IO.Async.Signal

import IO.Async.Type
import IO.Async.Loop.SignalH
import IO.Async.Util

%default total

parameters {auto has : Has Errno es}
           {auto sig : SignalH e}

  export
  awaitSignals : List Signal -> Async e es Siginfo
  awaitSignals s = do
    ev <- env
    primAsync $ \cb => primOnSignals ev s $ \case
      Right si => cb (Right si)
      Left x   => cb (Left $ inject x)

  export %inline
  onSignals : List Signal -> Async e es a -> Async e es a
  onSignals s act = ignore (awaitSignals s) >> act

  export %inline
  onSignal : Signal -> Async e es a -> Async e es a
  onSignal = onSignals . pure
