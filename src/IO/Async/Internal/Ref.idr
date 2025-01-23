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
  case casupdate1 r (\b => (False,b)) t of
    True  # t => act t
    False # t => () # t

export
put : (r : Ref t (Maybe a)) -> a -> (0 p : Res r rs) => F1' rs
put r v =
  casmod1 r $ \case
    Nothing => Just v
    Just w  => Just w

export
modify : (r : Ref t a) -> (a -> (a,b)) -> (0 p : Res r rs) => F1 rs b
modify r f t =
  let v1 # t := read1 r t
      (v2,res) := f v1
      _  # t := write1 r v2 t
   in res # t

export %inline
enqAt : IOArray n (Queue a) -> Fin n -> a -> IO1 ()
enqAt qs x v = casmodify qs x (`enqueue` v)

export %inline
deqAt : IOArray n (Queue a) -> Fin n -> IO1 (Maybe a)
deqAt qs x =
  casupdate qs x $ \q => case dequeue q of
    Just (v,q2) => (q2, Just v)
    Nothing     => (q, Nothing)
