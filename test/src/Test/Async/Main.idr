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

compute : Nat -> Nat -> Nat -> Nat
compute x y z = (x `minus` y) + z

applied : Async [] Nat
applied = [| compute lifted liftedAsync lifted |]

fromDo : Async [] Nat
fromDo = do
  x <- lifted
  y <- liftedAsync
  z <- lifted
  pure (compute x y z)

square : Nat -> Nat
square x = x * x

covering
coreSpecs : String -> Async [] Nat -> List FlatSpecInstr
coreSpecs str act =
  [ Desc str `should` "be returned unchanged" `at` (assert act val)
  ,   it `should` "be returned unchanged after mapping with id" `at`
        (assert (map id act) val)
  ,   it `should` "be returned unchanged after binding with pure" `at`
        (assert (act >>= pure) val)
  ,   it `should` "be returned unchanged after binding with `\\x => cede >> pure x`" `at`
        (assert (act >>= \x => cede >> pure x) val)
  ,   it `should` "be unchanged after a short delay" `at`
        (assert (delay 100.ms act) val)
  ,   it `should` "be unchanged after `cede`" `at` (assert (cede >> act) val)
  ,   it `should` "be squared after mapping with square" `at`
        (assert (map square act) (square val))
  ,   it `should` "be squared after binding with `pure . square`" `at`
        (assert (act >>= pure . square) (square val))
  ]

covering
main : IO ()
main =
  test $ 
    flatSpec "Async Spec" $
      coreSpecs "a natural number lifted with pure" lifted ++
      coreSpecs "a natural number lifted with async" liftedAsync ++
      coreSpecs "a natural number from idiom brackets" applied ++
      coreSpecs "a natural number from `do` notation" fromDo
