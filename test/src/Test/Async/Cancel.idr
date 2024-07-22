module Test.Async.Cancel

import Data.IORef
import Derive.Prelude
import Test.Async.Spec

%language ElabReflection
%default total

data Event : Type where
  Tick     : Event
  Tock     : Event
  Tack     : Event
  Canceled : Event

%runElab derive "Event" [Show,Eq]

parameters {auto ref : IORef (SnocList Event)}

  fire : Event -> Async [] ()
  fire e = modifyIORef ref (:< e) >> cede

  tick : Async [] ()
  tick = fire Tick

  tock : Async [] ()
  tock = fire Tock

  tack : Async [] ()
  tack = fire Tack

  onCncl : Async [] a -> Async [] a
  onCncl v = onCancel v (fire Canceled)

  onCnclB : Bool -> Async [] a -> Async [] a
  onCnclB True  v = onCncl v
  onCnclB False v = v

  tickTackTock : (cancel, masked : Bool) -> Async [] ()
  tickTackTock True True  =
    uncancelable (\_ => tick >> canceled >> tack) >> tock
  tickTackTock False True  =
    uncancelable (\_ => tick >> tack) >> tock
  tickTackTock True False  =
    tick >> canceled >> tack >> tock
  tickTackTock False False  =
    tick >> tack >> tock

  outer : (oncncl,masked : Bool) -> Async [] ()
  outer o m = do
    fbr <- start (onCnclB o $ tickTackTock False m)
    cede
    cancel fbr
    ignore $ join fbr

run : (IORef (SnocList Event) => Async [] ()) -> Async [] (List Event)
run f = do
  ref <- newIORef [<]
  fbr <- start (f @{ref})
  ignore $ join fbr
  map (<>> []) (readIORef ref)

covering
instrs : List FlatSpecInstr
instrs =
  [ "a fiber" `should` "run to completion if it's not canceled" `at`
      (assert (run $ tickTackTock False False) [Tick,Tack,Tock])
  , it `should` "not run `onCancel` hooks if it's not canceled" `at`
      (assert (run $ onCncl (tickTackTock False False)) [Tick,Tack,Tock])
  , it `should` "abort immediately after self-cancelation" `at`
      (assert (run $ tickTackTock True False) [Tick])
  , it `should` "run `onCancel` hooks after self-cancelation" `at`
      (assert (run $ onCncl (tickTackTock True False)) [Tick,Canceled])
  , it `should` "finish a masked region after self-cancelation" `at`
      (assert (run $ onCncl (tickTackTock True True)) [Tick,Tack,Canceled])
  , it `should` "abort immediately after cancelation from the outside" `at`
      (assert (run $ outer False False) [Tick])
  , it `should` "run `onCancel` hooks after cancelation from the outside" `at`
      (assert (run $ outer True False) [Tick,Canceled])
  , it `should` "finish a masked region after cancelation from the outside" `at`
      (assert (run $ outer True True) [Tick,Tack,Canceled])
  ]

export covering
specs : TestTree
specs = flatSpec "Cancel Spec" instrs
