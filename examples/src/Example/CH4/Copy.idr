module Example.CH4.Copy

import Opts

%default total

usage : String
usage =
  """
  Usage: async-examples copy SOURCE DEST [raw]

  Set `$LI_BUF_SIZE` to change the used buffer size (default: 65536).

  The `raw` options uses `readRaw` and `writeRaw` internally without
  reallocating a new buffer on every read. This allows us to get an idea
  of the cost of using immutable `ByteString`s versus reusing the same
  raw buffer. Spoiler: For small files (up to around 100 MB) the cost
  is very small. For larger files, reusing the same buffer starts to
  pay off probably due to garbage collection setting in in the other case.

  Note: To use this in a pipe, set SOURCE to /dev/stdin and/or
        DEST to /dev/stdout.
  """

parameters {auto hf : Has Errno es}

  covering
  cpRaw : Bits32 -> String -> String -> Prog es ()
  cpRaw buf i o =
    use [openFile i 0 0, openFile o create 0o660, cptr (cast buf)] $
      \[fi,fo,p] => streamp fi CPtr p (fwritenb fo)

  covering
  cp : Bits32 -> String -> String -> Prog es ()
  cp buf i o =
    use [openFile i 0 0, openFile o create 0o660] $
      \[fi,fo] => stream fi ByteString buf (fwritenb fo)

  export covering
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog [i,o] = do
    fi  <- readOptIO OPath i
    fo  <- readOptIO OPath o
    buf <- parseEnv OBits32 "LI_BUF_SIZE" 0x10000
    ignore $ cp buf fi fo
  prog [i,o,"raw"] = do
    fi  <- readOptIO OPath i
    fo  <- readOptIO OPath o
    buf <- parseEnv OBits32 "LI_BUF_SIZE" 0x10000
    ignore $ cpRaw buf fi fo
  prog _ = throw (WrongArgs usage)
