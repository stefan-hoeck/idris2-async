module IO.Async.Deferred

import Data.Linear.Ref1
import IO.Async.Internal.Loop
import IO.Async.Loop
import IO.Async.Type

%default total

-- internal state of a `Deferred1` value
data ST : Type -> Type where
  Ini : ST a
  Val : (v : a) -> ST a
  Obs : (cb : a -> IO1 ()) -> ST a

--------------------------------------------------------------------------------
-- Deferred1
--------------------------------------------------------------------------------

||| An atomic reference that can be set exactly once and observed
||| by at most one observer.
export
record Deferred1 a where
  constructor D1
  ref : IORef (ST a)

||| Creates a new, empty `Deferred1`.
export %inline
deferred1 : Lift1 World f => f (Deferred1 a)
deferred1 = D1 <$> newref Ini

||| Convenience alias of `Deferred1`, which takes the type of
||| the value stored as an explicit argument.
export %inline
deferred1Of : Lift1 World f => (0 a : _) -> f (Deferred1 a)
deferred1Of _ = deferred1

unobs1 : IORef (ST a) -> IO1 ()
unobs1 ref = casmod1 ref (const Ini)

||| Atomically tries to write the given value to a `Deferred1`.
|||
||| The value is written if and only if no other values has
||| been set first. Any observers will be invoked immediately.
export
put1 : Lift1 World f => Deferred1 a -> (v : a) -> f ()
put1 (D1 ref) v =
  lift1 $ \t =>
    let act # t := casupdate1 ref upd t
     in act t

  where
    upd : ST a -> (ST a, IO1 ())
    upd (Val x)  = (Val x, dummy)
    upd (Obs cb) = (Val v, cb v)
    upd Ini      = (Val v, dummy)

||| Waits (possibly by semantically blocking the fiber)
||| until a value is available from a `Deferred1`.
|||
||| Note: `Deferred1` values can only be observed
|||       by one observer. The calling fiber will block until
|||       canceled, if another fiber has called `await1` already.
export
await1 : Deferred1 a -> Async e es a
await1 (D1 ref) =
  primAsync $ \cb,t =>
    let act # t := casupdate1 ref (upd $ cb . Right) t
     in act t

  where
    upd : (a -> IO1 ()) -> ST a -> (ST a, IO1 (IO1 ()))
    upd cb (Val x) = (Val x, \t => let _ # t := cb x t in dummy # t)
    upd cb Ini     = (Obs cb, (unobs1 ref #))
    upd cb x       = (x, (dummy #))
