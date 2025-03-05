module IO.Async.Semaphore

import Data.Linear.Ref1
import Data.Nat
import IO.Async.Loop
import IO.Async.Type

%default total

-- internal state of a `Semaphore` value
data ST : Type where
  Available : (available : Nat) -> ST
  Requested : (requested : Nat) -> (cb : IO1 ()) -> ST

||| A semphore is a synchronization primitive that can
||| be observed by at most one observer.
|||
||| It consists of an internal counter that is atomically
||| reduced every time `release` is invoked.
|||
||| Calling `await` blocks the calling fiber until the
||| semaphore's counter has been reduced to 0.
export
record Semaphore where
  constructor S
  ref : IORef ST

||| Creates a new semaphore with an internal counter of `n`.
export %inline
semaphore : Lift1 World f => (n : Nat) -> f Semaphore
semaphore n = S <$> newref (Available n)

unobs : IORef ST -> IO1 ()
unobs ref =
  casmod1 ref $ \case
    Available n   => Available n
    Requested n _ => Available 0

||| Atomically reduces the internal counter of the semaphore by the
||| given number.
export
releaseN : HasIO io => Semaphore -> Nat -> io ()
releaseN _       0   = pure ()
releaseN (S ref) add =
  runIO $ \t =>
    let act # t := casupdate1 ref upd t
     in act t

  where
    upd : ST -> (ST, IO1 ())
    upd (Requested n cb) =
      case n `minus` add of
        0 => (Available (add `minus` n), cb)
        k => (Requested k cb, unit1)
    upd (Available n) = (Available $ n+add, unit1)

||| Atomically reduces the internal counter of the semaphore by one.
export %inline
release : HasIO io => Semaphore -> io ()
release s = releaseN s 1

||| Waits (possibly by semantically blocking the fiber)
||| until the given number of steps have been released.
|||
||| Note: Currently, `Semaphore` values can only be observed
|||       by one observer. The calling fiber will block until
|||       canceled, if another fiber has called `await` already.
export
acquireN : Semaphore -> Nat -> Async e es ()
acquireN (S ref) req =
  primAsync $ \cb,t =>
    let act # t := casupdate1 ref (upd $ cb (Right ())) t
     in act t

  where
    upd : IO1 () -> ST -> (ST, IO1 (IO1 ()))
    upd cb (Available n) =
      case n >= req of
        True  => (Available (n `minus` req), \t => let _ # t := cb t in unit1 # t)
        False => (Requested (req `minus` n) cb, (unobs ref #))
    upd cb x       = (x, (unit1 #))

||| Alias for `acquireN 1`
export %inline
acquire : Semaphore -> Async e es ()
acquire s = acquireN s 1
