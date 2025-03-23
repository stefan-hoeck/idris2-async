module IO.Async.File

import public System.Posix.File
import public IO.Async.Posix
import System
import System.File.Error

%default total

||| Opaque flag indicating that stdin has been set to
||| raw input mode.
export
data RawMode = RM

export
ELift1 World f => Resource f RawMode where
  cleanup rm = lift1 (ioToF1 resetRawMode)

||| Converts a `System.File.Error.FileError` to a POSIX error code
export
toErrno : FileError -> Errno
toErrno (GenericFileError i) = EN (cast i)
toErrno FileReadError        = EPERM
toErrno FileWriteError       = EPERM
toErrno FileNotFound         = ENOENT
toErrno PermissionDenied     = EACCES
toErrno FileExists           = EEXIST

parameters {auto has : Has Errno es}

  ||| Wraps an `IO` action from `System.File` in base by converting
  ||| file errors to POSIX error codes.
  export
  fileIO : IO (Either FileError a) -> Async e es a
  fileIO io =
    liftIO io >>= \case
      Left x => throw (toErrno x)
      Right v => pure v

  ||| Enables raw (unbuffered) input mode for stdin.
  |||
  ||| To make sure this is properly reset when the application ends,
  ||| wrap this in a call to `use` or `use1`:
  |||
  ||| ```idris
  ||| use1 rawMode $ \_ => your_code
  ||| ```
  export
  rawMode : Async e es RawMode
  rawMode = fileIO enableRawMode $> RM

  export %inline
  withFile : String -> Flags -> Mode -> (Fd -> Async e es a) -> Async e es a
  withFile pth fs m = use1 (openFile pth fs m)

  ||| Reads up to the given number of bytes from a file.
  export
  readFile : (0 r : Type) -> FromBuf r => String -> Bits32 -> Async e es r
  readFile r pth buf = withFile pth O_RDONLY 0 $ \fd => read fd r buf

  ||| Writes a value to an existing file.
  export
  writeFile : ToBuf r => String -> r -> Async e es ()
  writeFile pth v = withFile pth O_WRONLY 0 $ \fd => fwrite fd v

  ||| Writes a value to a file, creating it, if it does not yet exist.
  export
  createFile : ToBuf r => String -> Mode -> r -> Async e es ()
  createFile pth m v = withFile pth create m $ \fd => fwrite fd v

  ||| Appends a value to a file.
  |||
  ||| The file is created if it does not yet exist.
  export
  appendFile : ToBuf r => String -> Mode -> r -> Async e es ()
  appendFile pth m v = withFile pth append m $ \fd => fwrite fd v
