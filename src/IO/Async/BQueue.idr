module IO.Async.BQueue

import Data.Linear.Ref1
import Data.Linear.Unique
import Data.Queue
import IO.Async
import Syntax.T1

%default total

record Taker a where
  constructor T
  token    : IOToken
  callback : a -> IO1 ()

%inline
Eq (Taker a) where
  v1 == v2 = v1.token == v2.token

record Offerer a where
  constructor O
  token    : IOToken
  value    : a
  callback : IO1 ()

%inline
Eq (Offerer a) where
  v1 == v2 = v1.token == v2.token

-- internal state of the queue
record ST a where
  constructor S
  capacity : Nat
  queue    : Queue a
  takers   : Queue (Taker a)
  offerers : Queue (Offerer a)

%inline
takeV : Taker a -> a -> IO1 (IO1 ())
takeV (T _ cb) v t = let _ # t := cb v t in unit1 # t

%inline
takeO : Offerer a -> Taker a -> a -> IO1 (IO1 ())
takeO (O _ _ cb) tk v t = let _ # t := cb t in takeV tk v t

%inline
offer : Offerer a -> IO1 (IO1 ())
offer (O _ _ cb) t = let _ # t := cb t in unit1 # t

||| A concurrent, bounded queue holding values of type `a`.
|||
||| This is an important primitive for implementing producer/consumer
||| services.
export
record BQueue a where
  constructor BQ
  ref : IORef (ST a)

||| Creates a new bounded queue of the given capacity.
export %inline
bqueue : Lift1 World f => Nat -> f (BQueue a)
bqueue cap = BQ <$> newref (S cap empty empty empty)

||| Utility alias for `bqueue` taking the type of stored values
||| as an explicit argument.
export %inline
bqueueOf : Lift1 World f => (0 a : Type) -> Nat -> f (BQueue a)
bqueueOf _ = bqueue

%inline
untake : IORef (ST a) -> Taker a -> IO1 ()
untake r t = casmod1 r $ {takers $= filter (/= t)}

%inline
unoffer : IORef (ST a) -> Offerer a -> IO1 ()
unoffer r o = casmod1 r $ {offerers $= filter (/= o)}

deq : IORef (ST a) -> Taker a -> IO1 (IO1 ())
deq r tk t = let act # t := casupdate1 r adj t in act t
  where
    adj : ST a -> (ST a, IO1 (IO1 ()))
    adj (S cap q ts os) =
      case dequeue q of
        Just (n,q2) => case dequeue os of
          Nothing => (S (S cap) q2 ts os, takeV tk n)
          Just (o,os2) => (S cap (enqueue q2 o.value) ts os2, takeO o tk n)
        Nothing => case dequeue os of
          Nothing => (S cap q (enqueue ts tk) os, pure $ untake r tk)
          Just (o,os2) => (S cap q ts os2, takeO o tk o.value)

enq : IORef (ST a) -> Offerer a -> IO1 (IO1 ())
enq r o t = let act # t := casupdate1 r adj t in act t
  where
    adj : ST a -> (ST a, IO1 (IO1 ()))
    adj (S cap q ts os) =
      case dequeue ts of
        Just (t,ts2) => (S cap q ts2 os, takeO o t o.value)
        Nothing => case cap of
          0   => (S 0 q ts (enqueue os o), pure $ unoffer r o)
          S k => (S k (enqueue q o.value) ts os, offer o)

||| Appends a value to a bounded queue potentially blocking the
||| calling fiber until there is some capacity.
export
enqueue : BQueue a -> a -> Async e es ()
enqueue (BQ ref) v =
  primAsync $ \cb,t =>
   let tok # t := token1 t
    in enq ref (O tok v $ cb (Right ())) t

||| Extracts the next value from a bounded queue potentially blocking
||| the calling fiber until such a value is available.
export
dequeue : BQueue a -> Async e es a
dequeue (BQ ref) =
  primAsync $ \cb,t =>
   let tok # t := token1 t
    in deq ref (T tok $ cb . Right) t
