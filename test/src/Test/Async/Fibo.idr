module Test.Async.Fibo

import Data.List
import IO.Async.Loop.ThreadPool
import System

%default total

fibo : Nat -> Nat
fibo 0         = 1
fibo 1         = 1
fibo (S $ S k) = fibo k + fibo (S k)

sumFibos : Nat -> Nat -> Async WorkST [] ()
sumFibos nr fib = do
  vs <- parTraverse (\n => lazy (fibo n)) (replicate nr fib)
  printLn (maybe 0 sum vs)

sumVisFibos : Nat -> Nat -> Async WorkST [] ()
sumVisFibos nr fib = do
  vs <- parTraverse visFibo (replicate nr fib)
  printLn (maybe 0 sum vs)

  where
    visFibo : Nat -> Async WorkST [] Nat
    visFibo n = lazy (fibo n) >>= \x => printLn x $> x

covering
act : List String -> Async WorkST [] ()
act ["fibo",x,y]   = sumFibos (cast x) (cast y)
act ("fibo" :: _)  = sumFibos 1000 30
act ["vis_fibo",x,y] = sumVisFibos (cast x) (cast y)
act ("vis_fibo" :: _) = sumVisFibos 20 38
act _              = sumFibos 1000 30

covering
run : (threads : Nat) -> {auto 0 _ : IsSucc threads} -> List String -> IO ()
run threads args = do
  app threads $ act args
  usleep 100

covering
main : IO ()
main = do
  _::t <- getArgs | _ => die "Invalid arguments"
  s <- getEnv "IDRIS2_ASYNC_THREADS"
  case cast {to = Nat} <$> s of
    Just (S k) => run (S k) t
    _          => run 4 t
