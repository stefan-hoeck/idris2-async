module IO.Async.BQueue

import Data.Linear.Ref1
import Data.Linear.Deferred
import Data.Queue
import IO.Async

%default total

-- internal state of the queue
record ST a where
  constructor S
  capacity : Nat
  queue    : Queue a
  takers   : Queue (Once World a)
  offerers : Queue (a,Once World ())

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

deq : IORef (ST a) -> Poll (Async e) -> Once World a -> IO1 (Async e es a)
deq r poll def t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST a -> ST a -> IO1 (Async e es a)
    go x (S cap q ts os) t =
      case dequeue q of
        Just (n,q2) => case dequeue os of
          Nothing           => case caswrite1 r x (S (S cap) q2 ts os) t of
            True # t => pure n # t
            _    # t => deq r poll def t
          Just ((y,o), os2) => case caswrite1 r x (S cap (enqueue q2 y) ts os2) t of
            True # t => (putOnce o () $> n) # t
            _    # t => deq r poll def t
        Nothing     => case dequeue os of
          Nothing           => case caswrite1 r x (S cap q (enqueue ts def) os) t of
            True # t => poll (awaitOnce def) # t
            _    # t => deq r poll def t
          Just ((y,o), os2) => case caswrite1 r x (S cap q ts os2) t of
            True # t => (putOnce o () $> y) # t
            _    # t => deq r poll def t

enq : IORef (ST a) -> Poll (Async e) -> Once World () -> a -> IO1 (Async e es ())
enq r poll def n t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST a -> ST a -> IO1 (Async e es ())
    go x (S cap q ts os) t =
      case dequeue ts of
        Just (o,ts2) => case caswrite1 r x (S cap q ts2 os) t of
          True # t => putOnce o n # t
          _    # t => enq r poll def n t
        Nothing      => case cap of
          0   => case caswrite1 r x (S 0 q ts (enqueue os (n,def))) t of
            True # t => poll (awaitOnce def) # t
            _    # t => enq r poll def n t
          S k => case caswrite1 r x (S k (enqueue q n) ts os) t of
            True # t => pure () # t
            _    # t => enq r poll def n t

||| Appends a value to a bounded queue potentially blocking the
||| calling fiber until there is some capacity.
export
enqueue : BQueue a -> a -> Async e es ()
enqueue (BQ ref) v = do
  def <- onceOf ()
  uncancelable $ \poll => do
    act <- lift1 $ enq ref poll def v
    act

||| Extracts the next value from a bounded queue potentially blocking
||| the calling fiber until such a value is available.
export
dequeue : BQueue a -> Async e es a
dequeue (BQ ref) = do
  def <- onceOf a
  uncancelable $ \poll => do
    act <- lift1 $ deq ref poll def
    act
