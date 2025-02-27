module Test.Async.Token

import Data.SortedSet
import Data.List
import IO.Async.Unique
import Test.Async.Spec

%default total

units : List ()
units = replicate 100 ()

uniqueCount : Ord a => List a -> Nat
uniqueCount = length . SortedSet.toList . SortedSet.fromList

covering
instrs : List FlatSpecInstr
instrs =
  [ "`token`" `should` "generate a new unique token every time it is invoked" `at`
      (assert (uniqueCount <$> traverse (const token) units) 100)
  ]

export covering
specs : TestTree
specs = flatSpec "Token Spec" instrs
