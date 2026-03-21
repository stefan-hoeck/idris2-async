module Test.Async.BQueue

import IO.Async.BQueue

import Test.Async.Spec

%default total

cancelTakeThenPut : Async e [] Nat
cancelTakeThenPut = do
  q <- bqueueOf Nat 3
  f1 <- start {es=[]} $ dequeue q
  cede
  cancel f1
  enqueue q 1
  enqueue q 2
  dequeue q

cancelPutThenTake : Async e [] Nat
cancelPutThenTake = do
  q <- bqueueOf Nat 0
  f1 <- start {es=[]} $ enqueue q 1
  cede
  cancel f1
  f2 <- start {es=[]} $ enqueue q 2
  cede
  dequeue q

instrs : List (FlatSpecInstr e)
instrs =
  [ "a BQueue" `should` "not put values to a canceled taker" `at`
       (assert cancelTakeThenPut 1)
  , it `should` "not take values from a canceled offerer" `at`
       (assert cancelPutThenTake 2)
  ]

export covering
specs : TestTree e
specs = flatSpec "BQueue Spec" instrs
