module IO.Async.File

import public System.Posix.File
import public IO.Async.Posix

%default total

parameters {auto has : Has Errno es}
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
