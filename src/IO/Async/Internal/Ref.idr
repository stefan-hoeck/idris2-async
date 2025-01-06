||| Mutable references exposed in `PrimIO`. This includes the ability
||| to mutate via a CAS-loop to avoid locking with a mutex in certain
||| occasions.
module IO.Async.Internal.Ref

import Data.Array
import Data.Array.Mutable
import Data.Queue
import public IO.Async.Loop

%default total

export
modify : (r : Ref t a) -> (a -> (a,b)) -> (0 p : Res r rs) => F1 rs b
modify r f t =
  let v1 # t := read1 r t
      (v2,res) := f v1
      _  # t := write1 r v2 t
   in res # t

export
enqAt : IOArray n (Queue a) -> Fin n -> a -> IO1 ()
enqAt qs x v t =
 let q # t := get qs x t
  in set qs x (enqueue q v) t

export
deqAt : IOArray n (Queue a) -> Fin n -> IO1 (Maybe a)
deqAt qs x t =
 let q # t := get qs x t
     Just (v,q2) := dequeue q | Nothing => Nothing # t
     _ # t := set qs x q2 t
  in Just v # t
