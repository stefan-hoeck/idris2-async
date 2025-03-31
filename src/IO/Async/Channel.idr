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

rec : IORef (ST a) -> Poll (Async e) -> Once World (Maybe a) -> IO1 (Async e es (Maybe a))
rec r poll def t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST a -> ST a -> IO1 (Async e es (Maybe a))
    go x (S cap q ts os opn) t =
      case dequeue q of
        Just (n,q2) => case dequeue os of
          Nothing           => case caswrite1 r x (S (S cap) q2 ts os opn) t of
            True # t => pure (Just n) # t
            _    # t => rec r poll def t
          Just ((y,o), os2) => case caswrite1 r x (S cap (enqueue q2 y) ts os2 opn) t of
            True # t => (putOnce o (sendRes opn) $> Just n) # t
            _    # t => rec r poll def t
        Nothing     => case dequeue os of
          Nothing           => case opn of
            True  => case caswrite1 r x (S cap q (Just def) os opn) t of
              True # t => poll (awaitOnce def) # t
              _    # t => rec r poll def t
            False => pure Nothing # t
          Just ((y,o), os2) => case caswrite1 r x (S cap q ts os2 opn) t of
            True # t => (putOnce o (sendRes opn) $> Just y) # t
            _    # t => rec r poll def t

cls : IORef (ST a) -> IO1 (Async e es ())
cls r t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST a -> ST a -> IO1 (Async e es ())
    go x (S cap q ts os opn) t =
      case opn of
        False => pure () # t
        True  => case ts of
          Just def => case caswrite1 r x (S 0 empty Nothing empty False) t of
            True # t => putOnce def Nothing # t
            _    # t => cls r t
          Nothing  => case caswrite1 r x (S cap q ts os False) t of
            True # t => pure () # t
            _    # t => cls r t


snd : IORef (ST a) -> Poll (Async e) -> Once World SendRes -> a -> IO1 (Async e es SendRes)
snd r poll def n t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST a -> ST a -> IO1 (Async e es SendRes)
    go x (S cap q ts os opn) t =
      case opn of
        False  => pure Closed # t
        True   => case ts of
          Just o => case caswrite1 r x (S cap q Nothing os opn) t of
            True # t => (putOnce o (Just n) $> Sent) # t
            _    # t => snd r poll def n t
          Nothing  => case cap of
            0   => case caswrite1 r x (S 0 q ts (enqueue os (n,def)) opn) t of
              True # t => poll (awaitOnce def) # t
              _    # t => snd r poll def n t
            S k => case caswrite1 r x (S k (enqueue q n) ts os opn) t of
              True # t => pure Sent # t
              _    # t => snd r poll def n t

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
    act <- lift1 $ snd ref poll def v
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
  uncancelable $ \poll => do
    act <- lift1 $ rec ref poll def
    act

||| Gracefully closes the channel: No more data can be sent
||| (`send` will return immedately with `Closed` from now on),
||| put pending data can still be received.
export
close : Channel a -> Async e es ()
close (C ref) =
  uncancelable $ \poll => do
    act <- lift1 $ cls ref
    act
