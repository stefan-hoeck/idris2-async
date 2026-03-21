module IO.Async.Channel

import Data.Linear.Ref1
import Data.Linear.Unique
import Data.Queue
import Derive.Prelude
import IO.Async
import Syntax.T1

%default total
%language ElabReflection

public export
data SendRes = Sent | SentAndClosed | Closed

%runElab derive "SendRes" [Show,Eq,Ord]

sendRes : (opn : Bool) -> SendRes
sendRes True  = Sent
sendRes False = SentAndClosed

record Offerer a where
  constructor O
  token    : IOToken
  value    : a
  callback : SendRes -> IO1 ()

%inline
Eq (Offerer a) where
  v1 == v2 = v1.token == v2.token

0 Taker : Type -> Type
Taker a = Maybe a -> IO1 ()

-- internal state of the channel
record ST a where
  constructor S
  capacity : Nat
  queue    : Queue a
  taker    : Maybe (Taker a)
  offerers : Queue (Offerer a)
  open_    : Bool

%inline
takeV : Taker a -> Maybe a -> IO1 (IO1 ())
takeV cb v t = let _ # t := cb v t in unit1 # t

%inline
takeO : Bool -> Offerer a -> Taker a -> Maybe a -> IO1 (IO1 ())
takeO b (O _ _ cb) tk v t = let _ # t := cb (sendRes b) t in takeV tk v t

%inline
offer : SendRes -> Offerer a -> IO1 (IO1 ())
offer sr (O _ _ cb) t = let _ # t := cb sr t in unit1 # t

%inline
unrec : IORef (ST a) -> IO1 ()
unrec r = casmod1 r $ {taker := Nothing}

%inline
unoffer : IORef (ST a) -> Offerer a -> IO1 ()
unoffer r o = casmod1 r $ {offerers $= filter (/= o)}

rec : IORef (ST a) -> (Maybe a -> IO1 ()) -> IO1 (IO1 ())
rec r cb t = let act # t := casupdate1 r adj t in act t
  where
    adj : ST a -> (ST a, IO1 (IO1 ()))
    adj st@(S cap q ts os opn) =
      case dequeue q of
        Just (n,q2) => case dequeue os of
          Nothing => (S (S cap) q2 ts os opn, takeV cb $ Just n)
          Just (o, os2) =>
            (S cap (enqueue q2 o.value) ts os2 opn, takeO opn o cb $ Just n)
        Nothing => case dequeue os of
          Nothing => case opn of
            True  => (S cap q (Just cb) os opn, pure $ unrec r)
            False => (st, takeV cb Nothing)
          Just (o, os2) =>
            (S cap q ts os2 opn, takeO opn o cb $ Just o.value)

snd : IORef (ST a) -> Offerer a -> IO1 (IO1 ())
snd r o t = let act # t := casupdate1 r adj t in act t
  where
    adj : ST a -> (ST a, IO1 (IO1 ()))
    adj st@(S cap q ts os opn) =
     case opn of
       False => (st, offer Closed o)
       True  => case ts of
         Just cb => (S cap q Nothing os opn, takeO opn o cb $ Just o.value)
         Nothing => case cap of
           0 => (S 0 q ts (enqueue os o) opn, pure $ unoffer r o)
           S k => (S k (enqueue q o.value) ts os opn, offer Sent o)

cls : IORef (ST a) -> IO1 ()
cls r t = let act # t := casupdate1 r adj t in act t
  where
    adj : ST a -> (ST a, IO1 ())
    adj st@(S cap q ts os opn) =
      case opn of
        False => (st, unit1)
        True  => case ts of
          Just cb => (S 0 empty Nothing empty False, cb Nothing)
          Nothing => (S cap q ts os False, unit1)

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
send (C ref) v =
  primAsync $ \cb,t =>
   let tok # t := token1 t
    in Channel.snd ref (O tok v $ cb . Right) t

||| Extracts the next value from a channel potentially blocking
||| the calling fiber until such a value is available.
|||
||| This returns `Nothing` if the channel has been closed and
||| no pending values are left.
export
receive : Channel a -> Async e es (Maybe a)
receive (C ref) = primAsync $ \cb => Channel.rec ref (cb . Right)

||| Gracefully closes the channel: No more data can be sent
||| (`send` will return immedately with `Closed` from now on),
||| put pending data can still be received.
export
close : Channel a -> Async e es ()
close (C ref) = lift1 $ cls ref
