module Main

import Data.String

import Example.CH4.Copy
import Example.CH4.CopyWithHoles
import Example.CH4.Seek

import Example.CH63.Poll

import IO.Async.Loop.Poller

import Profile.Alloc
import Profile.Bind
import Profile.ChainedSpawn
import Profile.ParTraverse
import Profile.PingPong
import Profile.Scheduling
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
    "poll"                    :: t => Poll.prog t
    "profile-alloc"           :: t => Profile.Alloc.prog t
    "profile-bind"            :: t => Profile.Bind.prog t
    "profile-chained-spawn"   :: t => Profile.ChainedSpawn.prog t
    "profile-par-traverse"    :: t => Profile.ParTraverse.prog t
    "profile-ping-pong"       :: t => Profile.PingPong.prog t
    "profile-scheduling"      :: t => Profile.Scheduling.prog t
    "profile-spawn"           :: t => Profile.Spawn.prog t
    "profile-timer"           :: t => Profile.Timer.prog t
    _                              => stdoutLn usage

isProfiling : List String -> Bool
isProfiling (h::_) = "profile" `isPrefixOf` h
isProfiling []     = False

covering
main : IO ()
main = do
  _::t <- getArgs | _ => die "Invalid arguments"
  case isProfiling t of
    False => simpleApp $ handle handlers act
    True  => do
      n <- asyncThreads
      app n [] posixPoller (handle handlers act)
  exitSuccess

  where
    handlers : All (Handler () Poll) [Errno,ArgErr]
    handlers = [prettyOut,prettyOut]
