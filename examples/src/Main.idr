module Main

import Example.CH4.Copy
import Example.CH4.CopyWithHoles
import Example.CH4.Seek
import Opts
import System

%default total

usage : String
usage =
  """
  Usage: Install with `pack install-app async-examples` and then run with

         async-examples [prog] [args]...
  """

loop : Nat -> Prog es ()
loop 0     = pure ()
loop (S k) = pure () >> loop k

covering
act : Prog [Errno, ArgErr] ()
act = do
  (_::args) <- getArgs | [] => throw (WrongArgs usage)
  case args of
    ["--help"]                     => stdoutLn usage
    "copy"                    :: t => Copy.prog t
    "copyh"                   :: t => CopyWithHoles.prog t
    "seek"                    :: t => Seek.prog t
    "loop"                    :: t => loop 1_000_000
    _                              => stdoutLn usage

covering
run : (threads : Nat) -> {auto 0 _ : IsSucc threads} -> IO ()
run threads = app threads [] $ handle handlers act
  where
    handlers : All (Handler () EpollST) [Errno,ArgErr]
    handlers = [prettyOut,prettyOut]

covering
main : IO ()
main = do
  s <- getEnv "IDRIS2_ASYNC_THREADS"
  case cast {to = Nat} <$> s of
    Just (S k) => run (S k)
    _          => run 4
  exitSuccess
