module IO.Async.BQueue

import Data.Linear.Ref1
import Data.Queue
import IO.Async
import IO.Async.Deferred

%default total

-- internal state of the queue
record ST a where
  constructor S
  capacity : Nat
  queue    : Queue a
  takers   : Queue (Deferred a)
  offerers : Queue (a,Deferred ())

%inline
deq : Poll (Async e) -> Deferred a -> ST a -> (ST a, Async e es a)
deq poll def (S cap q ts os) =
  case dequeue q of
    Just (n,q2) => case dequeue os of
      Nothing           => (S (S cap) q2 ts os,  pure n)
      Just ((x,o), os2) => (S cap (enqueue q2 x) ts os2, put o () $> n)
    Nothing     => case dequeue os of
      Nothing           => (S cap q (enqueue ts def) os, poll (await def))
      Just ((x,o), os2) => (S cap q ts os2, put o () $> x)

%inline
enq : Poll (Async e) -> Deferred () -> a -> ST a -> (ST a, Async e es ())
enq poll def n (S cap q ts os) =
  case dequeue ts of
    Just (def,ts2) => (S cap q ts2 os, put def n)
    Nothing        => case cap of
      0   => (S 0 q ts (enqueue os (n,def)), poll (await def))
      S k => (S k (enqueue q n) ts os, pure ())

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

||| Appends a value to a bounded queue potentially blocking the
||| calling fiber until there is some capacity.
export
enqueue : BQueue a -> a -> Async e es ()
enqueue (BQ ref) v = do
  def <- deferredOf ()
  uncancelable $ \poll => do
    act <- update ref (enq poll def v)
    act

||| Extracts the next value from a bounded queue potentially blocking
||| the calling fiber until such a value is available.
export
dequeue : BQueue a -> Async e es a
dequeue (BQ ref) = do
  def <- deferredOf a
  uncancelable $ \poll => do
    act <- update ref (deq poll def)
    act
