module Main

import IO.Async.JS

%default total

prog : Async JS [] ()
prog = do
  sleep 200.ms
  putStrLn "slept for 200 ms"
  sleep 1.s
  putStrLn "slept for 1 s"
  fbs <- for [1..10] $ \i =>
    start {es = []} (sleep 1.s >> putStrLn "Fiber \{show i} done.")
  traverse_ wait fbs
  putStrLn "All work is done"

covering
main : IO ()
main = app prog
