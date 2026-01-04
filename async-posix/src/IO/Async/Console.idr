module IO.Async.Console

import Control.Monad.Resource
import Data.ByteString
import Data.String
import IO.Async.Core
import IO.Async.Logging
import IO.Async.Service
import System.Posix.File.Prim
import Text.ANSI

%default total

||| Record representing a console with
||| standard output and error output
public export
record ConsoleOut (0 e : Type) where
  constructor MkConsoleOut
  close_       : Async e [] ()
  putBytes_    : ByteString -> Async e [] ()
  putErrBytes_ : ByteString -> Async e [] ()

export %inline
Resource (Async e) (ConsoleOut e) where cleanup = close_

parameters {default 100 capacity : Nat}

  ||| Creates a console for writing messages and errors to.
  |||
  ||| To make this available to many fibers, this is run as a service
  ||| in the background using an internal buffer that can hold up to
  ||| `capacity` messages.
  export covering
  console :
       (putstr, puterr : ByteString -> Async e [] ())
    -> Async e es (ConsoleOut e)
  console putstr puterr = do
    srv <- stateless (const ()) putPair
    pure $ MkConsoleOut (cleanup srv) (send srv . (True,)) (send srv . (False,))

    where
      putPair : (Bool,ByteString) -> Async e [] ()
      putPair (True,s)  = putstr s
      putPair (False,s) = puterr s

  ||| The default console, printing to standard out and standard err.
  |||
  ||| Note: Since many fibers might be writing to the console at the same
  |||       this uses a bounded channel with a buffer of the given
  |||       capacity internally.
  export covering
  stdOut : Async e es (ConsoleOut e)
  stdOut =
    console
      (\bs => primIO $ Errno.ignore $ fwrite {es = [Errno]} Stdout bs)
      (\bs => primIO $ Errno.ignore $ fwrite {es = [Errno]} Stderr bs)

parameters {auto con : ConsoleOut e}

  ||| Put a bytestring to the console's standard output.
  export
  cputBytes : ByteString -> Async e es ()
  cputBytes s = weakenErrors $ con.putBytes_ s

  ||| Put a string to the console's standard output.
  export %inline
  cputStr : String -> Async e es ()
  cputStr = cputBytes . fromString
  
  ||| Put a string plus trailing line break
  ||| to the console's standard output.
  export %inline
  cputStrLn : String -> Async e es ()
  cputStrLn s = cputStr $ s ++ "\n"
  
  ||| Print a value to the console's standard output.
  export %inline
  cprint : Show a => a -> Async e es ()
  cprint = cputStr . show
  
  ||| Print a value plus trailing lne break
  ||| to the console's standard output.
  export %inline
  cprintLn : Show a => a -> Async e es ()
  cprintLn = cputStrLn . show

  ||| Put a bytestring to the console's error output.
  export
  cputErrBytes : ByteString -> Async e es ()
  cputErrBytes s = weakenErrors $ con.putErrBytes_ s
  
  ||| Put a string to the console's error output.
  export %inline
  cputErr : String -> Async e es ()
  cputErr = cputErrBytes . fromString
  
  ||| Put a string plus trailing line break
  ||| to the console's error output.
  export %inline
  cputErrLn : String -> Async e es ()
  cputErrLn s = cputErr $ s ++ "\n"
  
  ||| Print a value to the console's error output.
  export %inline
  cprintErr : Show a => a -> Async e es ()
  cprintErr = cputErr . show
  
  ||| Print a value plus trailing lne break
  ||| to the console's error output.
  export %inline
  cprintErrLn : Show a => a -> Async e es ()
  cprintErrLn = cputErrLn . show

--------------------------------------------------------------------------------
-- Console Logging
--------------------------------------------------------------------------------

export
consoleLogger :
     ConsoleOut e
  -> (LogLevel -> List String -> List String)
  -> Logger e
consoleLogger c f =
  MkLogger $ \l,ss => case l of
    Error => cputErr (unlines $ f l ss)
    Fatal => cputErr (unlines $ f l ss)
    _     => cputStr (unlines $ f l ss)

export
basicConsoleLogger : ConsoleOut e -> Logger e
basicConsoleLogger c =
  consoleLogger c $ \l => map $ \s => "[\{l}] \{s}"

col : LogLevel -> String
col Trace = show $ colored White "trace"
col Debug = show $ colored Cyan "debug"
col Info  = show $ colored Green "info"
col Warn  = show $ colored Yellow "warn"
col Error = show $ colored Red "error"
col Fatal = show $ colored Red "fatal"

space : LogLevel -> String
space Trace = " "
space Debug = " "
space Info  = "  "
space Warn  = "  "
space Error = " "
space Fatal = " "

||| A console logger with colored log level tags
export
colorConsoleLogger : ConsoleOut e -> Logger e
colorConsoleLogger c =
  consoleLogger c $ \l => map $ \s => "[\{col l}]\{space l}\{s}"

--------------------------------------------------------------------------------
--          Syslog
--------------------------------------------------------------------------------

severity : LogLevel -> Nat
severity Trace   = 7
severity Debug   = 7
severity Info    = 6
severity Warn    = 5
severity Error   = 4
severity Fatal   = 3

||| A logger using syslog priority codes. This can be used with
||| systemd services.
export
syslogLogger : ConsoleOut e -> Logger e
syslogLogger c =
  consoleLogger c $ \l => map $ \s => "<\{show $ severity l}> \{s}"
