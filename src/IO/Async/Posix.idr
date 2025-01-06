module IO.Async.Posix

import public IO.Async

import Data.Linear.Token
import Data.C.Ptr
import System.Posix.Dir
import System.Posix.File

%default total

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

export %inline
Has Errno es => ErrIO (Async e es) where
  eprim act =
    sync $ runIO $ \t => case act t of
      R r t => Right r # t
      E x t => Left (inject x) # t

export %inline
Resource (CArrayIO n a) where
  cleanup = liftIO . free

export %inline
Struct a => Resource a where
  cleanup = freeStruct

export %inline
Resource Dir where
  cleanup d = dropErrs {es = [Errno]} (closedir d)

namespace Fd
  export %inline
  Cast a Fd => Resource a where
    cleanup fd = dropErrs {es = [Errno]} (close fd)
