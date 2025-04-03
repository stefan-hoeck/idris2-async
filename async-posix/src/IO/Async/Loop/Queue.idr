module IO.Async.Loop.Queue

import Data.Array.Core as AC
import Data.Array.Mutable
import Data.Linear.Ref1
import Data.Nat

%default total

export
inc : IORef Nat -> IO1 ()
inc r t =
  assert_total $
   let v    # t := read1 r t
       True # t := caswrite1 r v (S v) t | _ # t => inc r t
    in () # t

export
dec : IORef Nat -> IO1 Bool
dec r t = assert_total $ let v # t := read1 r t in go v v t
  where
    go : Nat -> Nat -> IO1 Bool
    go x 0     t = False # t
    go x (S k) t =
      let True # t := caswrite1 r x k t | _ # t => dec r t
       in True # t

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

export
enq : IOArray n (Queue a) -> Fin n -> a -> IO1 Bool
enq r ix v t = assert_total $ let q # t := get r ix t in go q q t
  where
    go : Queue a -> Queue a -> IO1 Bool
    go x (Q as [] [<]) t = case casset r ix x (Q as [v] [<]) t of
      True # t => as # t
      _    # t => enq r ix v t
    go x (Q as h tl) t = case casset r ix x (Q as h (tl:<v)) t of
      True # t => as # t
      _    # t => enq r ix v t

export
enqall : IOArray n (Queue a) -> Fin n -> List a -> IO1 Bool
enqall r ix vs t = assert_total $ let q # t := get r ix t in go q q t
  where
    go : Queue a -> Queue a -> IO1 Bool
    go x (Q as [] [<]) t = case casset r ix x (Q as vs [<]) t of
      True # t => as # t
      _    # t => enqall r ix vs t
    go x (Q as h tl) t = case casset r ix x (Q as h (tl<><vs)) t of
      True # t => as # t
      _    # t => enqall r ix vs t

export
deq : IOArray n (Queue a) -> Fin n -> IO1 (Maybe a)
deq r ix t = assert_total $ let q # t := get r ix t in go q q t
  where
    go : Queue a -> Queue a -> IO1 (Maybe a)
    go x (Q as h tl) t =
      case h of
        y::z => case casset r ix x (Q False z tl) t of
          True # t => Just y # t
          _    # t => deq r ix t
        []   => case tl <>> [] of
          y::z => case casset r ix x (Q False z [<]) t of
            True # t => Just y # t
            _    # t => deq r ix t
          []   => Nothing # t

export
deqAndSleep : IOArray n (Queue a) -> Fin n -> IO1 (Maybe a)
deqAndSleep r ix t = assert_total $ let q # t := get r ix t in go q q t
  where
    go : Queue a -> Queue a -> IO1 (Maybe a)
    go x (Q as h tl) t =
      case h of
        y::z => case casset r ix x (Q False z tl) t of
          True # t => Just y # t
          _    # t => deq r ix t
        []   => case tl <>> [] of
          y::z => case casset r ix x (Q False z [<]) t of
            True # t => Just y # t
            _    # t => deq r ix t
          []   => case casset r ix x (Q True [] [<]) t of
            True # t => Nothing # t
            _    # t => deq r ix t

--------------------------------------------------------------------------------
-- Work stealing
--------------------------------------------------------------------------------

STEAL_MAX : Nat
STEAL_MAX = 10

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
steal : IOArray n (Queue a) -> Fin n -> IO1 (Maybe a)
steal r ix t = assert_total $ let q # t := get r ix t in go q q t
  where
    go : Queue a -> Queue a -> IO1 (Maybe a)
    go x (Q a hs ts) t =
      case ts of
        (rem:<v) => case casset r ix x (Q a hs rem) t of
          True # t => Just v # t
          _    # t => steal r ix t
        [<] => case hs of
          v::rem => case casset r ix x (Q a rem [<]) t of
            True # t => Just v # t
            _    # t => steal r ix t
          [] => Nothing # t
  -- where
  --   go : Queue a -> Queue a -> IO1 (List a)
  --   go x (Q _ [] [<]) t = [] # t
  --   go x (Q a h  [<]) t =
  --     let (h2,res) := splitHead h
  --      in case casset r ix x (Q a h2 [<]) t of
  --           True # t => res # t
  --           _    # t => steal r ix t
  --   go x (Q a h  tl)  t =
  --     let (tl2,res) := splitTail STEAL_MAX [] h tl
  --      in case casset r ix x (Q a h tl2) t of
  --           True # t => res # t
  --           _    # t => steal r ix t

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
