module Test.Async.Main

import Data.IORef
import Derive.Prelude
import Test.Async.Spec
import IO.Async.Sleep

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

val : Nat
val = 127

lifted : Async [] Nat
lifted = pure val

liftedAsync : Async [] Nat
liftedAsync = async $ \cb => cb (Right val)

square : Nat -> Nat
square x = x * x

covering
main : IO ()
main =
  test $ 
    flatSpec "Async Spec"
      [ "a natural number lifted with pure" `should` "be returned unchanged" `at`
            (assert lifted val)
      ,   it `should` "be returned unchanged after mapping with id" `at`
            (assert (map id lifted) val)
      ,   it `should` "be returned unchanged after binding with pure" `at`
            (assert (lifted >>= pure) val)
      ,   it `should` "be returned unchanged after binding with `\\x => cede >> pure x`" `at`
            (assert (lifted >>= \x => cede >> pure x) val)
      ,   it `should` "be unchanged by a short delay" `at`
            (assert (delay 100.ms lifted) val)
      ,   it `should` "be squared after mapping with square" `at`
            (assert (map square lifted) (square val))
      ,   it `should` "be squared after binding with `pure . square`" `at`
            (assert (lifted >>= pure . square) (square val))

      , "a natural number lifted with async" `should` "be returned unchanged" `at`
            (assert lifted val)
      ,   it `should` "be returned unchanged after mapping with id" `at`
            (assert (map id lifted) val)
      ,   it `should` "be returned unchanged after binding with pure" `at`
            (assert (lifted >>= pure) val)
      ,   it `should` "be returned unchanged after binding with `\\x => cede >> pure x`" `at`
            (assert (lifted >>= \x => cede >> pure x) val)
      ,   it `should` "be unchanged by a short delay" `at`
            (assert (delay 100.ms lifted) val)
      ,   it `should` "be squared after mapping with square" `at`
            (assert (map square lifted) (square val))
      ,   it `should` "be squared after binding with `pure . square`" `at`
            (assert (lifted >>= pure . square) (square val))
      ]
    -- Node "async"
    --   [ Node "binds"
    --       [ Leaf
    --           "chaining computations sequences effects"
    --           (assert (run $ tick >> tack >> tock) [Tick,Tack,Tock])
    --       , Leaf
    --           "replicating an effect runs it several times"
    --           (assert (run $ replicateM_ 6 tick) [Tick,Tick,Tick,Tick,Tick,Tick])

    --       ]
    --   ]
