module Main

import IO.Async.Loop.Epoll
import Test.Async.Cancel
import Test.Async.Core
import Test.Async.Race
import Test.Async.Spec

main : IO ()
main =
  epollApp $ test $
    Node "Async Spec"
      [ Core.specs
      , Cancel.specs
      , Race.specs
      ]
