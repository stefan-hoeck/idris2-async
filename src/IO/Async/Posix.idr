module IO.Async.Posix

import public IO.Async

import Data.C.Ptr
import System.Posix.Dir
import System.Posix.File

%default total

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

export %inline
ELift1 World f => Resource f Dir where
  cleanup d = dropErrs {es = [Errno]} (closedir d)

export %inline
ELift1 World f => Resource f CPtr where
  cleanup p = lift1 (freePtr1 p)

namespace Fd
  export %inline
  ELift1 World f => Cast a Fd => Resource f a where
    cleanup fd = dropErrs {es = [Errno]} (close fd)
