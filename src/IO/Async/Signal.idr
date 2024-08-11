module IO.Async.Signal

import IO.Async.Outcome
import IO.Async.Type
import IO.Async.Util
import public System.Signal

%default total

export covering
awaitSignal : Signal -> Async e es ()
awaitSignal s = ignore (collectSignal s) >> loop
  where
    covering
    loop : Async e es ()
    loop = do
      sleep 10.ms
      Just x <- handleNextCollectedSignal | Nothing => loop
      when (s /= x) loop

export covering %inline
onSignal : Signal -> Async e es a -> Async e es a
onSignal s act = awaitSignal s >> act
