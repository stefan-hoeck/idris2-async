module Test.Async.Race

import Derive.Prelude
import Test.Async.Spec

%language ElabReflection
%default total

data Event : Type where
  Outer    : Event
  Tick     : Event
  Tock     : Event
  Tack     : Event
  Canceled : Event

%runElab derive "Event" [Show,Eq]

parameters {auto ref : IORef (SnocList (Nat,Event))}

  fire : Nat -> Event -> Async e es ()
  fire n e = runIO (mod1 ref (:< (n,e))) >> cede

  tick : Nat -> Async e es ()
  tick n = fire n Tick

  tock : Nat -> Async e es ()
  tock n = fire n Tock

  tack : Nat -> Async e es ()
  tack n = fire n Tack

  onCncl : Nat -> Async e es a -> Async e es a
  onCncl n v = onCancel v (fire n Canceled)

  events : Nat -> List Event -> Async e es ()
  events k []        = pure ()
  events k (x :: xs) = fire k x >> events k xs

  rce : List Event -> List Event -> Async e es ()
  rce xs ys =
    ignore $ race2
      (onCncl 1 $ events 1 xs)
      (onCncl 2 $ events 2 ys)

run : (IORef (SnocList (Nat,Event)) => Async e es ()) -> Async e es (List (Nat,Event))
run f = do
  ref <- newIORef [<]
  fbr <- start (f @{ref})
  ignore $ join fbr
  map (<>> []) (runIO (read1 ref))

-- Note: The fiber that loses the race will fire one more event
-- before being canceled, because the main fiber will awoken
-- and appended to the event queue *after* the winning fiber
-- finished.
covering
instrs : List FlatSpecInstr
instrs =
  [ "a race" `should` "cancel the second fiber after the first is done" `at`
      (assert (run $ rce [Tick] [Tick,Tack,Tock]) [(1,Tick),(2,Tick),(2,Tack),(2,Canceled)])
  , it `should` "cancel the first fiber after the second is done" `at`
      (assert (run $ rce [Tick,Tack,Tock,Tick] [Tick]) [(1,Tick),(2,Tick),(1,Tack),(1,Tock),(1,Canceled)])
  ]

export covering
specs : TestTree
specs = flatSpec "Race Spec" instrs
