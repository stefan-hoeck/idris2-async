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
  head   : List a
  tail   : SnocList a

export %inline
queueOf : (0 a : Type) -> Queue a
queueOf _ = Q False [] [<]

export
isEmpty : Queue a -> Bool
isEmpty (Q _ [] [<]) = True
isEmpty _            = False

||| Enqueues a value returning whether the loop belonging to
||| this queue is currently running.
|||
||| This can be invoked from any thread.
export %inline
enq : a -> Queue a -> (Queue a, Bool)
enq pkg (Q asleep [] [<]) = (Q asleep [pkg] [<], asleep)
enq pkg (Q asleep h  t)   = (Q asleep h (t:<pkg), asleep)

||| Enqueues a list of values.
|||
||| This happens only during work stealing, so we set the `asleep`
||| flag to `False`.
export %inline
enqall : List a -> Queue a -> Queue a
enqall pkgs (Q asleep [] [<]) = Q False pkgs [<]
enqall pkgs (Q asleep h  t)   = Q False h (t <>< pkgs)

||| Removes the first task from the queue.
|||
||| This is only invoked from the loop running the queue,
||| so the `asleep` flag is always set to `False`.
export %inline
deq : Queue a -> (Queue a, Maybe a)
deq (Q asleep h t) =
  case h of
    x::y => (Q False y t, Just x)
    []   => case t <>> [] of
      x::y => (Q False y [<], Just x)
      []   => (Q False [] [<], Nothing)

||| Like `deq`, but sets the `asleep` flag to `True` in case
||| no item was found. This is used as the last step before
||| sending the current loop to sleep.
export %inline
deqAndSleep : Queue a -> (Queue a,Maybe a)
deqAndSleep (Q asleep h t) =
  case h of
    x::y => (Q False y t, Just x)
    []   => case t <>> [] of
      x::y => (Q False y [<], Just x)
      []   => (Q True [] [<], Nothing)

--------------------------------------------------------------------------------
-- Work stealing
--------------------------------------------------------------------------------

STEAL_MAX : Nat
STEAL_MAX = 2

-- we want to steal at most half + 1 tasks from the head of a
-- queue, so this counts elements from the head two at a time.
-- we also don't want to steal more than `STEAL_MAX` tasks
count : List a -> Nat -> Nat
count []         k     = 0
count _          0     = 0
count [_]        _     = 1
count (_::_::xs) (S k) = S (count xs k)

-- like `count` but for the tail
countsl : SnocList a -> Nat -> Nat
countsl [<]        k     = 0
countsl _          0     = 0
countsl [<_]       _     = 1
countsl (sx:<_:<_) (S k) = S (countsl sx k)

splitList : SnocList a -> Nat -> List a -> (List a, List a)
splitList sx (S k) (x::xs) = splitList (sx:<x) k xs
splitList sx _     xs      =(xs, sx <>> [])

splitSnoc : SnocList a -> Nat -> List a -> (SnocList a, List a)
splitSnoc (sx:<x) (S k) xs = splitSnoc sx k (x::xs)
splitSnoc sx      _     xs = (sx, xs)

splitHead : List a -> (List a, List a)
splitHead xs = splitList [<] (count xs STEAL_MAX) xs 

splitTail : Nat -> List a -> List a -> SnocList a -> (SnocList a, List a)
splitTail (S n) res (_::t) (i:<v) = splitTail n (v::res) t i
splitTail 0     res _      sx     = (sx, res)
splitTail n     res _      [<]    = ([<], res)
splitTail n     res []     sx     =
  splitSnoc sx (countsl sx n) res

||| Steals up to `STEAL_MAX` tasks from a queue but not more than half
||| the enqueued tasks (rounded up).
export
steal : Queue a -> (Queue a,List a)
steal st@(Q _ [] [<]) = (st,[])
steal (Q a h [<])     = let (h2,res) := splitHead h in (Q a h2 [<],res)
steal (Q a h t)       = let (t2,res) := splitTail STEAL_MAX [] h t in (Q a h t2,res)

--------------------------------------------------------------------------------
-- Tests and Proofs
--------------------------------------------------------------------------------

0 count1 : (n : Nat) -> count [] n === 0
count1 _ = Refl

0 count2 : (n : Nat) -> (xs : List a) -> LTE (count xs n) n
count2 0 []            = LTEZero
count2 0 (x :: xs)     = LTEZero
count2 (S k) []        = LTEZero
count2 (S k) [x]       = LTESucc LTEZero
count2 (S k) (_::_::xs)= LTESucc (count2 k xs)

0 count3 : (n : Nat) -> (xs : List a) -> LTE (count xs n) (length xs)
count3 0 []            = LTEZero
count3 0 (x :: xs)     = LTEZero
count3 (S k) []        = LTEZero
count3 (S k) [x]       = LTESucc LTEZero
count3 (S k) (_::_::xs)= lteSuccRight (LTESucc $ count3 k xs)

0 count4 : count [1,2,3,4,5] 2 === 2
count4 = Refl

0 count5 : count [1,2,3,4] 2 === 2
count5 = Refl

0 count6 : count [1,2,3] 2 === 2
count6 = Refl

0 count7 : count [1,2] 2 === 1
count7 = Refl

0 countsl1 : (n : Nat) -> countsl [<] n === 0
countsl1 _ = Refl

0 countsl2 : (n : Nat) -> (sx : SnocList a) -> LTE (countsl sx n) n
countsl2 0 [<]           = LTEZero
countsl2 0 (sx :< x)     = LTEZero
countsl2 (S k) [<]       = LTEZero
countsl2 (S k) [<x]      = LTESucc LTEZero
countsl2 (S k) (sx:<_:<_)= LTESucc (countsl2 k sx)

0 countsl3 : (n : Nat) -> (sx : SnocList a) -> LTE (countsl sx n) (length sx)
countsl3 0 [<]           = LTEZero
countsl3 0 (sx:<x)       = LTEZero
countsl3 (S k) [<]       = LTEZero
countsl3 (S k) [<x]      = LTESucc LTEZero
countsl3 (S k) (sx:<_:<_)= lteSuccRight (LTESucc $ countsl3 k sx)

0 countsl4 : countsl [<1,2,3,4,5] 2 === 2
countsl4 = Refl

0 countsl5 : countsl [<1,2,3,4] 2 === 2
countsl5 = Refl

0 countsl6 : countsl [<1,2,3] 2 === 2
countsl6 = Refl

0 countsl7 : countsl [<1,2] 2 === 1
countsl7 = Refl
