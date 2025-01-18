module Example.CH4.Seek

import Opts
import Pretty

%default total

usage : String
usage =
  """
  Usage: async-examples seek DEST [cmd]...

  Commands:
  s[offset] seek to the given offset
  r[length] read `length` bytes and display them as text
  R[length] read `length` bytes and display them in hexadecimal
  w[str]    write string `str` at the given position

  Usage example:

    async-examples seek out s1000000000 whello

    This will create or edit file `out` and write "hello" after
    moving to position 1000000000. The first 10^9 bytes will consist of
    a single hole and not occupy any space on disk.

    This can easily be verified by displaying the allocated size of
    the file with `ls -ls`. Please check also the different behavior
    of `async-examples copy` and `async-examples copyh` when copying
    such a file.
  """

data Cmd : Type where
  Seek    : OffT   -> Cmd
  Read    : Bits32 -> Cmd
  ReadHex : Bits32 -> Cmd
  Write   : String -> Cmd

readCmd : String -> Either ArgErr Cmd
readCmd s =
  case unpack s of
    's' :: t => Seek    <$> readOpt OOff (pack t)
    'r' :: t => Read    <$> readOpt OBits32 (pack t)
    'R' :: t => ReadHex <$> readOpt OBits32 (pack t)
    'w' :: t => Right (Write $ pack t)
    _        => Left $ WrongArgs usage

rd : Bool -> Bits32 -> String
rd False n = "r\{show n}"
rd True  n = "R\{show n}"

disp : Bool -> ByteString -> String
disp False = toString
disp True  = toHexString (Just ':')

parameters {auto hf : Has Errno es}

  readHere : Bool -> Fd -> Bits32 -> Prog es ()
  readHere b fd n = read fd _ n >>= \x => stdoutLn "\{rd b n}: \{disp b x}"

  seek : List Cmd -> (fd : Fd) -> Prog es ()
  seek []        fd = pure ()
  seek (x :: xs) fd = cmd x >> seek xs fd
    where
      cmd : Cmd -> Prog es ()
      cmd (Seek i)    = do
        o <- lseek fd i SEEK_SET
        stdoutLn "s\{show i}: moved to \{show o}"

      cmd (Read m)    = readHere False fd m
      cmd (ReadHex m) = readHere True  fd m

      cmd (Write str) =
        write fd str >>= \n => stdoutLn "s\{str}: wrote \{show n} bytes"

  export
  prog : Has ArgErr es => List String -> Prog es ()
  prog ["--help"] = stdoutLn usage
  prog (i::t) = do
    fi <- readOptIO OPath i
    cs <- injectEither (traverse readCmd t)
    withFile fi (O_RDWR <+> O_CREAT) 0o666 (seek cs)
  prog _ = throw (WrongArgs usage)
