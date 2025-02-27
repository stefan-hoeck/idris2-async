module IO.Async.Deferred

import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.SortedMap
import IO.Async.Internal.Loop
import IO.Async.Loop
import IO.Async.Type
import IO.Async.Unique

%default total

-- internal state of a `Deferred` value
data ST : Type -> Type where
  Val : (v : a) -> ST a
  Obs : (cbs : SortedMap Token (a -> IO1 ())) -> ST a

-- internal state of a `Deferred1` value
data ST1 : Type -> Type where
  Ini1 : ST1 a
  Val1 : (v : a) -> ST1 a
  Obs1 : (cb : a -> IO1 ()) -> ST1 a

--------------------------------------------------------------------------------
-- Deferred1
--------------------------------------------------------------------------------

||| An atomic reference that can be set exactly once and observed
||| by at most one observer.
|||
||| There are many occasions when it is enough to be able to register
||| only one observer. Use `Deferred1` for these, and use `Deferred` in
||| case you need to register many observers.
export
record Deferred1 a where
  constructor D1
  ref : IORef (ST1 a)

||| Creates a new, empty `Deferred1`.
export %inline
deferred1 : Lift1 World f => f (Deferred1 a)
deferred1 = D1 <$> newref Ini1

||| Convenience alias of `Deferred1`, which takes the type of
||| the value stored as an explicit argument.
export %inline
deferred1Of : Lift1 World f => (0 a : _) -> f (Deferred1 a)
deferred1Of _ = deferred1

unobs1 : IORef (ST1 a) -> IO1 ()
unobs1 ref =
  casmod1 ref $ \case
    Obs1 _ => Ini1
    v      => v

||| Reads the set value of a `Deferred1`. Returns `Nothing`,
||| if no value has been set yet.
export %inline
peek1 : Lift1 World f => Deferred1 a -> f (Maybe a)
peek1 (D1 ref) =
  lift1 $ \t =>
    let Val1 x # t := read1 ref t | _ # t => Nothing # t
     in Just x # t

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
    upd : ST1 a -> (ST1 a, IO1 ())
    upd (Val1 x)  = (Val1 x, dummy)
    upd (Obs1 cb) = (Val1 v, cb v)
    upd Ini1      = (Val1 v, dummy)

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
    upd : (a -> IO1 ()) -> ST1 a -> (ST1 a, IO1 (IO1 ()))
    upd cb (Val1 x) = (Val1 x, \t => let _ # t := cb x t in dummy # t)
    upd cb Ini1     = (Obs1 cb, (unobs1 ref #))
    upd cb x       = (x, (dummy #))

--------------------------------------------------------------------------------
-- Deferred
--------------------------------------------------------------------------------

||| An atomic reference that can be set exactly once and observed
||| by an arbitrary number of observers.
export
record Deferred a where
  constructor D
  ref : IORef (ST a)

||| Creates a new, empty `Deferred1`.
export %inline
deferred : Lift1 World f => f (Deferred a)
deferred = D <$> newref (Obs empty)

||| Convenience alias of `Deferred`, which takes the type of
||| the value stored as an explicit argument.
export %inline
deferredOf : Lift1 World f => (0 a : _) -> f (Deferred a)
deferredOf _ = deferred

unobs : Token -> IORef (ST a) -> IO1 ()
unobs tok ref =
  casmod1 ref $ \case
    Obs cbs => Obs $ delete tok cbs
    v       => v

||| Reads the set value of a `Deferred`. Returns `Nothing`,
||| if no value has been set yet.
export %inline
peek : Lift1 World f => Deferred a -> f (Maybe a)
peek (D ref) =
  lift1 $ \t =>
    let Val x # t := read1 ref t | _ # t => Nothing # t
     in Just x # t

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
    upd (Val x)   = (Val x, dummy)
    upd (Obs cbs) = (Val v, traverse1_ (\cb => cb v) (Prelude.toList cbs))

||| Waits (possibly by semantically blocking the fiber)
||| until a value is available from a `Deferred1`.
|||
||| Note: `Deferred1` values can only be observed
|||       by one observer. The calling fiber will block until
|||       canceled, if another fiber has called `await1` already.
export
await : Deferred a -> Async e es a
await (D ref) = do
  tok <- token
  primAsync $ \cb,t =>
    let act # t := casupdate1 ref (upd tok $ cb . Right) t
     in act t

  where
    upd : Token -> (a -> IO1 ()) -> ST a -> (ST a, IO1 (IO1 ()))
    upd tok cb (Val x)   = (Val x, \t => let _ # t := cb x t in dummy # t)
    upd tok cb (Obs cbs) = (Obs (insert tok cb cbs), (unobs tok ref #))
