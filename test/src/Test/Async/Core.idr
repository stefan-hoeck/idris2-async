module Test.Async.Core

import Test.Async.Spec

%default total

val : Nat
val = 127

lifted : Async e es Nat
lifted = pure val

liftedAsync : Async e es Nat
liftedAsync = primAsync_ $ \cb => cb (Right val)

compute : Nat -> Nat -> Nat -> Nat
compute x y z = (x `minus` y) + z

applied : Async e es Nat
applied = [| compute lifted liftedAsync lifted |]

fromDo : Async e es Nat
fromDo = do
  x <- lifted
  y <- liftedAsync
  z <- lifted
  pure (compute x y z)

square : Nat -> Nat
square x = x * x

covering
instrs : String -> Async SyncST [Errno] Nat -> List FlatSpecInstr
instrs str act =
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

export covering
specs : TestTree
specs =
  flatSpec "Core Spec" $
    instrs "a natural number lifted with pure" lifted ++
    instrs "a natural number lifted with async" liftedAsync ++
    instrs "a natural number from idiom brackets" applied ++
    instrs "a natural number from `do` notation" fromDo
