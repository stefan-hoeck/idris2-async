module IO.Async.Loop.PollH

import public IO.Async
import public System.Posix.File
import public System.Posix.Poll.Types

%default total

public export
interface PollH a where
  threadId : a -> Nat
  primPoll :
       a
    -> Fd
    -> PollEvent
    -> (autoClose : Bool)
    -> (Either Errno PollEvent -> IO1 ())
    -> IO1 (IO1 ())
