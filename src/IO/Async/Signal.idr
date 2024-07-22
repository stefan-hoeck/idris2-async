module IO.Async.Signal

import IO.Async.Fiber
import IO.Async.Outcome
import public System.Signal

%default total

||| Semantically blocks the current fiber until the given signal is
||| encountered.
export covering
blockTill : Has SignalError es => Signal -> Async es ()
blockTill sig = injectIO (collectSignal sig) >> go
  where
    go : Async es ()
    go = do
      cede
      v <- handleNextCollectedSignal
      unless (v == Just sig) go
