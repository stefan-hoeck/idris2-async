module IO.Async.Deferred

import Data.Linear.Ref1
import IO.Async.Internal.Loop
import IO.Async.Loop
import IO.Async.Type

%default total

-- internal state of a `Deferred` value
data ST : Type -> Type where
  Ini : ST a
  Val : (v : a) -> ST a
  Obs : (cb : a -> IO1 ()) -> ST a

||| An atomic reference that can be set exactly once and observed
||| by at most one observer.
export
record Deferred a where
  constructor D
  ref : IORef (ST a)

||| Creates a new, empty `Deferred`.
export %inline
deferred : Lift1 World f => f (Deferred a)
deferred = D <$> newref Ini

||| Convenience alias of `Deferred`, which takes the type of
||| the value stored as an explicit argument.
export %inline
deferredOf : Lift1 World f => (0 a : _) -> f (Deferred a)
deferredOf _ = deferred

unobs : IORef (ST a) -> IO1 ()
unobs ref = casmod1 ref (const Ini)

||| Atomically tries to write the given value to a `Deferred`.
|||
||| The value is written if and only if no other values has
||| been set first. Any observers will be invoked immediately.
export
put : Lift1 World f => Deferred a -> (v : a) -> f ()
put (D ref) v =
  lift1 $ \t =>
    let act # t := casupdate1 ref upd t
     in act t

  where
    upd : ST a -> (ST a, IO1 ())
    upd (Val x)  = (Val x, dummy)
    upd (Obs cb) = (Val v, cb v)
    upd Ini      = (Val v, dummy)

||| Waits (possibly by semantically blocking the fiber)
||| until a value is available from a `Deferred`.
|||
||| Note: Currently, `Deferred` values can only be observed
|||       by one observer. The calling fiber will block until
|||       canceled, if another fiber has called `await` already.
export
await : Deferred a -> Async e es a
await (D ref) =
  primAsync $ \cb,t =>
    let act # t := casupdate1 ref (upd $ cb . Right) t
     in act t

  where
    upd : (a -> IO1 ()) -> ST a -> (ST a, IO1 (IO1 ()))
    upd cb (Val x) = (Val x, \t => let _ # t := cb x t in dummy # t)
    upd cb Ini     = (Obs cb, (unobs ref #))
    upd cb x       = (x, (dummy #))
