module Profile.All

import Opts

import Profile.Alloc
import Profile.Async2
import Profile.Bind
import Profile.ChainedSpawn
import Profile.Consumers
import Profile.ParTraverse
import Profile.PingPong
import Profile.Race
import Profile.Scheduling
import Profile.Spawn
import Profile.Util

%default total

export covering
prog : Has Errno es => Prog es ()
prog = do
  stdout "Alloc:          " >> Alloc.measure
  stdout "Async2:         " >> Async2.measure 100_000_000
  stdout "Bind:           " >> Bind.measure 1_000_000_000
  stdout "Chained Spawn:  " >> ChainedSpawn.measure 10_000_000
  stdout "Consumers:      " >> Consumers.measure 1000
  stdout "Par Traverse:   " >> ParTraverse.measure 1_000_000
  stdout "Ping Pong:      " >> PingPong.measure 1_000_000
  stdout "Race (trivial): " >> Race.measure "trivial" 1_000_000
  stdout "Race (single):  " >> Race.measure "single" 1_000_000
  stdout "Race (both):    " >> Race.measure "both" 1_000_000
  stdout "Scheduling:     " >> Scheduling.measure
  stdout "Spawn:          " >> Spawn.measure 10_000_000
