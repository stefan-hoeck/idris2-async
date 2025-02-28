module Test.Async.Main

import Test.Async.Cancel
import Test.Async.Core
import Test.Async.Race
import Test.Async.Spec

covering
main : IO ()
main =
  test $ 
    Node "Async Spec"
      [ Core.specs
      , Cancel.specs
      , Race.specs
      ]
