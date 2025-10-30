module Test.Async.Main

import IO.Async.Loop.Sync
import Test.Async.Cancel
import Test.Async.Core
import Test.Async.Race
import Test.Async.Spec

covering
main : IO ()
main = do
  snc <- sync
  runAsync snc $ runTree $ 
    Node "Async Spec"
      [ Core.specs
      , Cancel.specs
      , Race.specs
      ]
