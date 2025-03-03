module IO.Async.Semaphore

import Data.Linear.Ref1
import Data.Nat
import IO.Async.Loop
import IO.Async.Type

%default total

-- internal state of a `Semaphore` value
data ST : Type where
  Ini : Nat -> ST
  Obs : Nat -> (cb : IO1 ()) -> ST

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
semaphore n = S <$> newref (Ini n)

unobs : IORef ST -> IO1 ()
unobs ref =
  casmod1 ref $ \case
    Ini n   => Ini n
    Obs n _ => Ini n

||| Atomically reduces the internal counter of the semaphore by one.
export
release : HasIO io => Semaphore -> io ()
release (S ref) =
  runIO $ \t =>
    let act # t := casupdate1 ref upd t
     in act t

  where
    upd : ST -> (ST, IO1 ())
    upd (Obs n cb) =
      case pred n of
        0 => (Ini 0, cb)
        k => (Obs k cb, unit1)
    upd (Ini n) = (Ini $ pred n, unit1)

||| Atomically reduces the internal counter of the semaphore to zero.
export
releaseAll : HasIO io => Semaphore -> io ()
releaseAll (S ref) =
  runIO $ \t =>
    let act # t := casupdate1 ref upd t
     in act t

  where
    upd : ST -> (ST, IO1 ())
    upd (Obs n cb) = (Ini 0, cb)
    upd _          = (Ini 0, unit1)

||| Waits (possibly by semantically blocking the fiber)
||| until the semaphore has been released down to zero.
|||
||| Note: Currently, `Semaphore` values can only be observed
|||       by one observer. The calling fiber will block until
|||       canceled, if another fiber has called `await` already.
export
await : Semaphore -> Async e es ()
await (S ref) =
  primAsync $ \cb,t =>
    let act # t := casupdate1 ref (upd $ cb (Right ())) t
     in act t

  where
    upd : IO1 () -> ST -> (ST, IO1 (IO1 ()))
    upd cb (Ini 0) = (Ini 0, \t => let _ # t := cb t in unit1 # t)
    upd cb (Ini n) = (Obs n cb, (unobs ref #))
    upd cb x       = (x, (unit1 #))
