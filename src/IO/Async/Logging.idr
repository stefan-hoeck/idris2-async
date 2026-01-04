module IO.Async.Logging

import IO.Async.Core
import Derive.Prelude

%default total
%language ElabReflection

public export
data LogLevel = Trace | Debug | Info | Warn | Error | Fatal

%runElab derive "LogLevel" [Show,Eq,Ord]

export
Interpolation LogLevel where interpolate = toLower . show

public export
record Logger (0 e : Type) where
  constructor MkLogger
  logML : LogLevel -> Lazy (List String) -> Async e [] ()

||| Only log message of at least the given logging level.
export
filter : LogLevel -> Logger e -> Logger e
filter lvl x = MkLogger $ \l,s => case l >= lvl of
  True  => x.logML l s
  False => pure ()

export
Semigroup (Logger e) where
  x <+> y = MkLogger $ \l,s => x.logML l s >> y.logML l s

export
Monoid (Logger e) where
  neutral = MkLogger $ \_,_ => pure ()

parameters {auto lg  : Logger e}

  export
  logML : LogLevel -> Lazy (List String) -> Async e es ()
  logML l ss = weakenErrors $ lg.logML l ss 

  export %inline
  log : LogLevel -> Lazy String -> Async e es ()
  log l s = logML l [s]
  
  export %inline
  trace : Lazy String -> Async e es ()
  trace = log Trace
  
  export %inline
  debug : Lazy String -> Async e es ()
  debug = log Debug
  
  export %inline
  info : Lazy String -> Async e es ()
  info = log Info
  
  export %inline
  warn : Lazy String -> Async e es ()
  warn = log Warn
  
  export %inline
  error : Lazy String -> Async e es ()
  error = log Error
  
  export %inline
  fatal : Lazy String -> Async e es ()
  fatal = log Fatal
  
  export %inline
  traceML : Lazy (List String) -> Async e es ()
  traceML = logML Trace
  
  export %inline
  debugML : Lazy (List String) -> Async e es ()
  debugML = logML Debug
  
  export %inline
  infoML : Lazy (List String) -> Async e es ()
  infoML = logML Info
  
  export %inline
  warnML : Lazy (List String) -> Async e es ()
  warnML = logML Warn
  
  export %inline
  errorML : Lazy (List String) -> Async e es ()
  errorML = logML Error
  
  export %inline
  fatalML : Lazy (List String) -> Async e es ()
  fatalML = logML Fatal
  
  export %inline
  ierror : Interpolation a => a -> Async e es ()
  ierror x = error (interpolate x)
  
  export %inline
  ifatal : Interpolation a => a -> Async e es ()
  ifatal x = fatal (interpolate x)
