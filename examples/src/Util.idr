module Util

import public Data.C.Ptr
import public IO.Async
import public IO.Async.File
import public IO.Async.Loop.Epoll
import public IO.Async.Posix

%default total

public export
0 Prog : List Type -> Type -> Type
Prog = Async EpollST

parameters {auto has : Has Errno es}

  export covering
  stream :
       {auto fid : FileDesc a}
    -> (0 r : Type)
    -> {auto frb : FromBuf r}
    -> (fd : a)
    -> (buffer : Bits32)
    -> (r -> Prog es ())
    -> Prog es Bool
  stream r fd buf run =
    readres fd r buf >>= \case
      EOI         => pure True
      Closed      => pure False
      NoData      => stream r fd buf run
      Interrupted => stream r fd buf run
      Res v       => run v >> stream r fd buf run


