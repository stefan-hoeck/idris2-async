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
unobs r t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST -> ST -> IO1 ()
    go x (Available n) t = () # t
    go x _             t =
      case caswrite1 r x (Available 0) t of
        True # t => () # t
        _    # t => unobs r t

rel : IORef ST -> Nat -> IO1 ()
rel r add t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST -> ST -> IO1 ()
    go x (Requested n cb) t =
      case n `minus` add of
        0 => case caswrite1 r x (Available (add `minus` n)) t of
          True # t => cb t
          _    # t => rel r add t
        k => case caswrite1 r x (Requested k cb) t of
          True # t => () # t
          _    # t => rel r add t
    go x (Available n) t =
      case caswrite1 r x (Available $ n + add) t of
        True # t => () # t
        _    # t => rel r add t

||| Atomically reduces the internal counter of the semaphore by the
||| given number.
export
releaseN : HasIO io => Semaphore -> Nat -> io ()
releaseN _       0   = pure ()
releaseN (S ref) add = runIO (rel ref add)

||| Atomically reduces the internal counter of the semaphore by one.
export %inline
release : HasIO io => Semaphore -> io ()
release s = releaseN s 1

acq : IORef ST -> Nat -> IO1 () -> IO1 (IO1 ())
acq r req cb t = assert_total $ let x # t := read1 r t in go x x t
  where
    go : ST -> ST -> IO1 (IO1 ())
    go x (Available n) t =
      case n >= req of
        True  => case caswrite1 r x (Available (n `minus` req)) t of
          True # t => let _ # t := cb t in unit1 # t
          _    # t => acq r req cb t
        False => case caswrite1 r x (Requested (req `minus` n) cb) t of
          True # t => unobs r # t
          _    # t => acq r req cb t
    go x _ t = unit1 # t

||| Waits (possibly by semantically blocking the fiber)
||| until the given number of steps have been released.
|||
||| Note: Currently, `Semaphore` values can only be observed
|||       by one observer. The calling fiber will block until
|||       canceled, if another fiber has called `await` already.
export
acquireN : Semaphore -> Nat -> Async e es ()
acquireN (S ref) req = primAsync $ \cb => acq ref req (cb (Right ()))

||| Alias for `acquireN 1`
export %inline
acquire : Semaphore -> Async e es ()
acquire s = acquireN s 1
