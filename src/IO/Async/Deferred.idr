module IO.Async.Deferred

import Data.Linear.Ref1
import IO.Async
import IO.Async.Internal.Loop
import IO.Async.Loop

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
deferred : HasIO io => io (Deferred a)
deferred = D <$> newIORef Ini

||| Convenience alias of `Deferred`, which takes the type of
||| the value stored as an explicit argument.
export %inline
deferredOf : HasIO io => (0 a : _) -> io (Deferred a)
deferredOf _ = deferred

unobs : IORef (ST a) -> Bool -> IO1 ()
unobs ref _ = casmod1 ref (const Ini)

||| Atomically tries to write the given value to a `Deferred`.
|||
||| The value is written if and only if no other values has
||| been set first. Any observers will be invoked immediately.
export
put : HasIO io => Deferred a -> (v : a) -> io ()
put (D ref) v =
  runIO $ \t =>
    let act # t := casupdate1 ref upd t
     in act t

  where
    upd : ST a -> (ST a, IO1 ())
    upd (Val x)  = (Val x, dummy)
    upd (Obs cb) = (Val v, cb v)
    upd Ini      = (Val v, dummy)

||| Waits (possibly by semantically blocking the fiber)
||| until a value is available from a `Deferred`.
export
await : Deferred a -> Async e es a
await (D ref) =
  primAsync $ \cb,t =>
    let act # t := casupdate1 ref (upd $ cb . Right) t
     in act t

  where
    upd : (a -> IO1 ()) -> ST a -> (ST a, IO1 (Bool -> IO1 ()))
    upd cb (Val x) = (Val x, \t => let _ # t := cb x t in const dummy # t)
    upd cb _       = (Obs cb, (unobs ref #))
