module Example.CH63.Poll

import Data.List1
import Data.String
import System.Posix.Time
import Opts

%default total

usage : String
usage =
  """
  Usage: async-examples poll secs[/nsecs][:int-secs[/int-nsecs]]

  Sets up and observes a (possibly repeating) timer via a file descriptor.
  In addition, asynchronously reads from stdin.
  """

prettyClock : Clock t -> Clock t -> String
prettyClock now start =
  let cl  := timeDifference now start
      ns  := nanoseconds cl `div` 10_000_000
      nss := padLeft 2 '0' (show ns)
   in padLeft 7 ' ' "\{show $ seconds cl}.\{nss}"

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}
  
  covering
  sleepLoop : Clock Duration -> Maybe (Clock Duration) -> Prog es ()
  sleepLoop once rep = do
    start <- liftIO (clockTime Monotonic)
    sleep once
    now <- liftIO (clockTime Monotonic)
    stdoutLn "\{prettyClock now start}: 0 tick(s)"
    go 1 start

    where
      covering
      go : Nat -> Clock Monotonic -> Prog es ()
      go n start =
        case rep of
          Nothing => pure ()
          Just r  => do
            sleep r
            now <- liftIO (clockTime Monotonic)
            stdoutLn "\{prettyClock now start}: \{show n} tick(s)"
            go (S n) start

  covering
  readLoop : Prog es ()
  readLoop = do
    bs <- readnb Stdin ByteString 4
    stdoutLn "got \{show bs.size} bytes from stdin"
    readLoop

  readPair : String -> Prog es (TimeT,NsecT)
  readPair s =
    case forget $ split ('/' ==) s of
      [x]   => (,0) <$> readOptIO OTime x
      [x,y] => [| MkPair (readOptIO OTime x) (readOptIO ONsecT y) |]
      _     => throw (WrongArgs usage)
  
  readSpec : String -> Prog es (Clock Duration, Maybe $ Clock Duration)
  readSpec s =
    case forget $ split (':' ==) s of
      [x]   => do
        (s,n) <- readPair x
        pure $ (duration s n, Nothing)
      [x,y] => do
        (s,n)   <- readPair x
        (si,ni) <- readPair y
        pure $ (duration s n, Just $ duration si ni)
      _     => throw (WrongArgs usage)
  
  covering
  app : (t : String) -> Prog es ()
  app t = do
    (o,rep) <- readSpec t
    race_ [readLoop, sleepLoop o rep]
  
  export covering
  prog : List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [s]        = app s
  prog args       = throw (WrongArgs usage)
