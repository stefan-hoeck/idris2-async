module IO.Async.Sleep

import IO.Async.Fiber
import System.Clock

%default total

||| Returns the current system monotonic time.
|||
||| This is strictly increasing and therefore useful for
||| computing time deltas.
export %inline
clockMonotonic : Async es (Clock Monotonic)
clockMonotonic = liftIO (clockTime Monotonic)

||| Returns the current system UTC time
export %inline
clockUTC : Async es (Clock UTC)
clockUTC = liftIO (clockTime UTC)

||| The zero duration.
export %inline
zero : Clock Duration
zero = makeDuration 0 0

||| Delay a computation by the given number of nanoseconds.
export
sleep : Clock Duration -> Async es ()
sleep d = unless (d <= zero) $ clockMonotonic >>= go
  where
    go : Clock Monotonic -> Async es ()
    go t = do
      c <- clockMonotonic
      unless (timeDifference c t >= d) (cede >> go (assert_smaller t t))

||| Delay a computation by the given number of nanoseconds.
export %inline
delay : Clock Duration -> Async es a -> Async es a
delay d act = sleep d >> act

||| Creates a duration of `n` seconds
export
(.s) : (n : Nat) -> Clock Duration
n.s = makeDuration (cast n) 0

||| Creates a duration of `n` nanoseconds
export
(.ns) : (n : Nat) -> Clock Duration
n.ns = makeDuration 0 (cast n)

||| Creates a duration of `n` microseconds
export
(.us) : (n : Nat) -> Clock Duration
n.us = (n * 1_000).ns

||| Creates a duration of `n` milliseconds
export
(.ms) : (n : Nat) -> Clock Duration
n.ms = (n * 1_000_000).ns
