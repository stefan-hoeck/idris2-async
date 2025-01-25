module Main

import Example.CH4.Copy
import Example.CH4.CopyWithHoles
import Example.CH4.Seek

import Profile.Bind
import Profile.ChainedSpawn
import Profile.ParTraverse
import Profile.Spawn
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

covering
act : Prog [Errno, ArgErr] ()
act = do
  (_::args) <- getArgs | [] => throw (WrongArgs usage)
  case args of
    ["--help"]                     => stdoutLn usage
    "copy"                    :: t => Copy.prog t
    "copyh"                   :: t => CopyWithHoles.prog t
    "seek"                    :: t => Seek.prog t
    "profile-bind"            :: t => Profile.Bind.prog t
    "profile-chained-spawn"   :: t => Profile.ChainedSpawn.prog t
    "profile-par-traverse"    :: t => Profile.ParTraverse.prog t
    "profile-spawn"           :: t => Profile.Spawn.prog t
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

