module Test.Async.Race

import Control.Monad.MCancel
import Derive.Prelude
import Test.Async.Spec

%language ElabReflection
%default total

data Event : Type where
  Outer    : Nat -> Event
  Tick     : Nat -> Event
  Tock     : Nat -> Event
  Tack     : Nat -> Event
  Canceled : Nat -> Event
  None     : Event
  RNat     : Nat -> Event
  RErr     : String -> Event

%runElab derive "Event" [Show,Eq]

toEvent : Outcome [String] (Maybe $ Either Nat Nat) -> Event
toEvent (Succeeded Nothing)          = None
toEvent (Succeeded (Just (Left x)))  = RNat x
toEvent (Succeeded (Just (Right x))) = RNat x
toEvent (Error $ Here x)             = RErr x
toEvent Canceled                     = None

parameters {auto ref : IORef (SnocList Event)}

  fire : Event -> Async e es ()
  fire e = runIO (mod1 ref (:< e)) >> cede

  tick : Nat -> Async e es ()
  tick = fire . Tick

  tock : Nat -> Async e es ()
  tock = fire . Tock

  tack : Nat -> Async e es ()
  tack = fire . Tack

  onCncl : Nat -> Async e es a -> Async e es a
  onCncl n v = onCancel v (fire $ Canceled n)

  events : Nat -> List (Nat -> Event) -> Async e es Nat
  events k []        = pure k
  events k (x :: xs) =
    case x k of
      Canceled _ => canceled $> k
      _          => fire (x k) >> events k xs

  rce :
       List (Nat -> Event)
    -> List (Nat -> Event)
    -> Async e [String] (Maybe $ Either Nat Nat)
  rce xs ys =
    race2
      (onCncl 1 $ events 1 xs)
      (onCncl 2 $ events 2 ys)

run :
     (IORef (SnocList Event) => Async e [String] (Maybe $ Either Nat Nat))
  -> Async e es (List Event)
run f = do
  ref <- newref [<]
  fbr <- start (f @{ref})
  out <- join fbr
  runIO (mod1 ref (:< toEvent out))
  map (<>> []) (runIO (read1 ref))

-- Note: The fiber that loses the race will fire one more event
-- before being canceled, because the main fiber will be awoken
-- and appended to the event queue *after* the winning fiber
-- finished.
covering
instrs : List FlatSpecInstr
instrs =
  [ "a race" `should` "cancel the second fiber after the first is done" `at`
      (assert
        (run $ rce [Tick] [Tick,Tack,Tock])
        [Tick 1,Tick 2,Tack 2,Canceled 2, RNat 1])
  , it `should` "cancel the first fiber after the second is done" `at`
      (assert
        (run $ rce [Tick,Tack,Tock,Tick] [Tick])
        [Tick 1,Tick 2,Tack 1,Tock 1,Canceled 1, RNat 2])
  , it `should` "return the result of the second fiber right after the first was canceled" `at`
      (assert
        (run $ rce [Tick,Tack,Canceled] [Tick,Tack])
        [Tick 1, Tick 2, Tack 1, Tack 2, Canceled 1, RNat 2])
  , it `should` "return the result of the first fiber right after the second was canceled" `at`
      (assert
        (run $ rce [Tick,Tack] [Tick,Canceled])
        [Tick 1, Tick 2, Tack 1, Canceled 2, RNat 1])
  ]

export covering
specs : TestTree
specs = flatSpec "Race Spec" instrs
