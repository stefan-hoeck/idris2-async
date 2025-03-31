||| Mutable references exposed in `PrimIO`. This includes the ability
||| to mutate via a CAS-loop to avoid locking with a mutex in certain
||| occasions.
module IO.Async.Internal.Ref

import Data.Array
import Data.Array.Mutable
import Data.Queue
import public IO.Async.Loop

%default total

||| Guaranteed to run the given cleanup function exactly once:
||| The boolean flag is atomically read and set to false before running the
||| cleanup hook, and `act` is only run if the flag has been `True`.
export
once : (r : IORef Bool) -> (act : IO1 ()) -> IO1 ()
once r act t =
  assert_total $ case read1 r t of
    True # t => case caswrite1 r True False t of
      True # t => act t
      _    # t => once r act t
    _ # t => () # t
