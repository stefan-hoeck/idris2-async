module Main

import IO.Async.Loop.Epoll
import IO.Async.File
import IO.Async.Posix

%default total

main : IO ()
main = putStrLn "Hello World"
