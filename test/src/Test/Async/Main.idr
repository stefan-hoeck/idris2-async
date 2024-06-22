module Test.Async.Main

import IO.Async

%default total

replicateM_ : Applicative f => Nat -> f () -> f ()
replicateM_ 0     _ = pure ()
replicateM_ (S k) x = x *> replicateM_ k x

wait : Nat -> Async [] ()
wait n = replicateM_ n cede

tick : Async [] ()
tick = wait 2 >> putStrLn "tick"

tock : Async [] ()
tock = wait 5 >> putStrLn "  tock"

tack : Async [] ()
tack = wait 1 >> putStrLn "    tack"

prog : Async [] ()
prog =
  ignore $ unsafePar
    [ replicateM_ 25 tick
    , replicateM_ 10 tock
    , replicateM_ 50 tack
    ]

covering
main : IO ()
main = sync >>= \_ => runAsync prog

