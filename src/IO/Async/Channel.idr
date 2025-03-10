module IO.Async.Channel

import Data.Linear.Ref1
import Data.Linear.Deferred
import Data.Queue
import Derive.Prelude
import IO.Async

%default total
%language ElabReflection

public export
data SendRes = Sent | SentAndClosed | Closed

%runElab derive "SendRes" [Show,Eq,Ord]

sendRes : (opn : Bool) -> SendRes
sendRes True  = Sent
sendRes False = SentAndClosed

-- internal state of the channel
record ST a where
  constructor S
  capacity : Nat
  queue    : Queue a
  taker    : Maybe (Once World $ Maybe a)
  offerers : Queue (a,Once World SendRes)
  open_    : Bool

%inline
rec : Once World (Maybe a) -> ST a -> (ST a, Async e es (Maybe a))
rec def st@(S cap q ts os opn) =
  case dequeue q of
    Just (n,q2) => case dequeue os of
      Nothing           => (S (S cap) q2 ts os opn, pure (Just n))
      Just ((x,o), os2) => (S cap (enqueue q2 x) ts os2 opn, putOnce o (sendRes opn) $> Just n)
    Nothing     => case dequeue os of
      Nothing           => case opn of
        True  => (S cap q (Just def) os opn, (awaitOnce def))
        False => (st, pure Nothing)
      Just ((x,o), os2) => (S cap q ts os2 opn, putOnce o (sendRes opn) $> Just x)

%inline
cls : ST a -> (ST a, Async e es ())
cls st@(S cap q ts os opn) =
  case opn of
    False => (st, pure ())
    True  => case ts of
      Just def => (S 0 empty Nothing empty False, putOnce def Nothing)
      Nothing  => (S cap q ts os False, pure ())

%inline
snd :
     Poll (Async e)
  -> Once World SendRes
  -> a
  -> ST a
  -> (ST a, Async e es SendRes)
snd poll def n st@(S cap q ts os opn) =
  case opn of
    False  => (st, pure Closed)
    True   => case ts of
      Just def => (S cap q Nothing os opn, putOnce def (Just n) $> Sent)
      Nothing  => case cap of
        0   => (S 0 q ts (enqueue os (n,def)) opn, poll (awaitOnce def))
        S k => (S k (enqueue q n) ts os opn, pure Sent)

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
channel cap = C <$> newref (S cap empty empty empty True)

||| Utility alias for `channel` taking the type of stored values
||| as an explicit argument.
export %inline
channelOf : Lift1 World f => (0 a : Type) -> Nat -> f (Channel a)
channelOf _ = channel

||| Sends a value through a channel potentially blocking the
||| calling fiber until there is some capacity.
|||
||| This returns
|||   * `Sent` if the data was received and the channel is still open after sending
|||   * `SentAndClosed` if the data was received and the channel is now closed
|||   * `Closed` if the data could not be sent since the channel is closed.
export
send : Channel a -> a -> Async e es SendRes
send (C ref) v = do
  def <- onceOf SendRes
  uncancelable $ \poll => do
    act <- update ref (snd poll def v)
    act

||| Extracts the next value from a channel potentially blocking
||| the calling fiber until such a value is available.
|||
||| This returns `Nothing` if the channel has been closed and
||| no pending values are left.
export
receive : Channel a -> Async e es (Maybe a)
receive (C ref) = do
  def <- onceOf (Maybe a)
  act <- update ref (rec def)
  act
  -- uncancelable $ \poll => do
  --   act <- update ref (rec poll def)
  --   act

||| Gracefully closes the channel: No more data can be sent
||| (`send` will return immedately with `Closed` from now on),
||| put pending data can still be received.
export
close : Channel a -> Async e es ()
close (C ref) =
  uncancelable $ \poll => do
    act <- update ref cls
    act
