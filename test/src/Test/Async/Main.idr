module Test.Async.Main

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

replicateM_ : Applicative f => Nat -> f () -> f ()
replicateM_ 0     _ = pure ()
replicateM_ (S k) x = x *> replicateM_ k x

wait : Nat -> Async [] ()
wait n = replicateM_ n cede

parameters {auto ref : IORef (SnocList Event)}

  fire : Event -> Async [] ()
  fire e = modifyIORef ref (:< e)

  tick : Async [] ()
  tick = wait 2 >> fire Tick

  tock : Async [] ()
  tock = wait 5 >> fire Tock

  tack : Async [] ()
  tack = wait 1 >> fire Tack

  onCncl : Async [] a -> Async [] a
  onCncl v = onCancel v (fire Canceled)

run : (IORef (SnocList Event) => Async [] ()) -> Async [] (List Event)
run f = do
  ref <- newIORef [<]
  f @{ref}
  map (<>> []) (readIORef ref)

covering
main : IO ()
main =
  test $
    Node "async"
      [ Node "binds"
          [ Leaf
              "chaining computations sequences effects"
              (assert (run $ tick >> tack >> tock) [Tick,Tack,Tock])
          , Leaf
              "replicating an effect runs it several times"
              (assert (run $ replicateM_ 6 tick) [Tick,Tick,Tick,Tick,Tick,Tick])

          ]
      ]
