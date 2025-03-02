module Util

import public Data.C.Ptr
import public IO.Async
import public IO.Async.Loop.ThreadPool
import public IO.Async.File
import public IO.Async.Posix

%default total

public export
0 Prog : List Type -> Type -> Type
Prog = Async Poll

export %inline
prettyOut : HasIO io => Interpolation a => a -> io ()
prettyOut = stdoutLn . interpolate
