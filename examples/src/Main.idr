module Main

import Example.CH4.Copy
import Example.CH4.CopyWithHoles
import Example.CH4.Seek

import Profile.Timer

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
    "profile-timer"           :: t => Profile.Timer.prog t
    _                              => stdoutLn usage

covering
main : IO ()
main = do
  simpleApp $ handle handlers act
  exitSuccess

  where
    handlers : All (Handler () EpollST) [Errno,ArgErr]
    handlers = [prettyOut,prettyOut]

