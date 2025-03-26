module IO.Async.Loop.Queue

import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Task Queue and basic operations
--------------------------------------------------------------------------------

||| A specialize queue implementation enabling fast enqueue, dequeue,
||| and work stealing.
export
record Queue a where
  constructor Q
  asleep : Bool
  tail   : SnocList a

export %inline
queueOf : (0 a : Type) -> Queue a
queueOf _ = Q False [<]

export
isEmpty : Queue a -> Bool
isEmpty (Q _ [<]) = True
isEmpty _         = False

||| Enqueues a value returning whether the loop belonging to
||| this queue is currently running.
|||
||| This can be invoked from any thread.
export %inline
enq : a -> Queue a -> (Queue a, Bool)
enq pkg (Q asleep t) = (Q asleep (t:<pkg), asleep)

||| Removes first tasks from the queue.
|||
||| This is only invoked from the loop running the queue,
||| so the `asleep` flag is always set to `False`.
export %inline
deq : Queue a -> (Queue a, SnocList a)
deq (Q asleep t) = (Q False [<], t)

||| Like `deq`, but sets the `asleep` flag to `True` in case
||| no item was found. This is used as the last step before
||| sending the current loop to sleep.
export %inline
deqAndSleep : Queue a -> (Queue a,SnocList a)
deqAndSleep (Q _ [<]) = (Q True [<], [<])
deqAndSleep (Q _ st)  = (Q False [<], st)
