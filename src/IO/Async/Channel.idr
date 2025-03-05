module IO.Async.Channel

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
  taker    : Maybe (Once World a)
  offerers : Queue (a,Once World ())

%inline
rec : Poll (Async e) -> Once World a -> ST a -> (ST a, Async e es a)
rec poll def (S cap q ts os) =
  case dequeue q of
    Just (n,q2) => case dequeue os of
      Nothing           => (S (S cap) q2 ts os,  pure n)
      Just ((x,o), os2) => (S cap (enqueue q2 x) ts os2, putOnce o () $> n)
    Nothing     => case dequeue os of
      Nothing           => (S cap q (Just def) os, poll (awaitOnce def))
      Just ((x,o), os2) => (S cap q ts os2, putOnce o () $> x)

%inline
snd : Poll (Async e) -> Once World () -> a -> ST a -> (ST a, Async e es ())
snd poll def n (S cap q ts os) =
  case ts of
    Just def => (S cap q Nothing os, putOnce def n)
    Nothing  => case cap of
      0   => (S 0 q ts (enqueue os (n,def)), poll (awaitOnce def))
      S k => (S k (enqueue q n) ts os, pure ())

||| A concurrent, bounded channel holding values of type `a`.
|||
||| This is an important primitive for implementing single
||| consumer, multiple producer services.
|||
||| Note: Unlike with `IO.Async.BQueue`, which can have multiple
|||       consumers, this will only accpet a single consumer,
|||       silently overwriting an old consumer in case a new one
|||       calls.
export
record Channel a where
  constructor C
  ref : IORef (ST a)

||| Creates a new bounded queue of the given capacity.
export %inline
channel : Lift1 World f => Nat -> f (Channel a)
channel cap = C <$> newref (S cap empty empty empty)

||| Utility alias for `channel` taking the type of stored values
||| as an explicit argument.
export %inline
channelOf : Lift1 World f => (0 a : Type) -> Nat -> f (Channel a)
channelOf _ = channel

||| Sends a value through a channel potentially blocking the
||| calling fiber until there is some capacity.
export
send : Channel a -> a -> Async e es ()
send (C ref) v = do
  def <- onceOf ()
  uncancelable $ \poll => do
    act <- update ref (snd poll def v)
    act

||| Extracts the next value from a channel potentially blocking
||| the calling fiber until such a value is available.
export
receive : Channel a -> Async e es a
receive (C ref) = do
  def <- onceOf a
  uncancelable $ \poll => do
    act <- update ref (rec poll def)
    act
