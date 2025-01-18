module Pretty

import Data.Bits
import Data.ByteString
import Data.List
import Data.SortedMap
import Data.String
import System.Posix.Process
import System.Posix.Signal

%default total

hexChar : Bits8 -> Char
hexChar 0   = '0'
hexChar 1   = '1'
hexChar 2   = '2'
hexChar 3   = '3'
hexChar 4   = '4'
hexChar 5   = '5'
hexChar 6   = '6'
hexChar 7   = '7'
hexChar 8   = '8'
hexChar 9   = '9'
hexChar 10  = 'A'
hexChar 11  = 'B'
hexChar 12  = 'C'
hexChar 13  = 'D'
hexChar 14  = 'E'
hexChar _   = 'F'

toHex : Bits8 -> List Char
toHex m = [hexChar $ shiftR m 4, hexChar $ m .&. 15]

export
toHexString : (sep : Maybe Char) -> ByteString -> String
toHexString sep = pack . dropSep . foldr acc []

  where
    dropSep : List Char -> List Char
    dropSep []     = []
    dropSep (h::t) = maybe (h::t) (const t) sep

    acc : Bits8 -> List Char -> List Char
    acc v cs = toList sep ++ toHex v ++ cs

export
hex : Nat -> Bits64 -> String
hex n = go []
  where
    go : List Char -> Bits64 -> String
    go cs 0 = "0x\{padLeft n '0' $ pack cs}"
    go cs x =
      go (hexChar (cast $ x .&. 0xf) :: cs) (assert_smaller x $ shiftR x 4)

cdStr : Bool -> String
cdStr True  = " (core dumped)"
cdStr False = ""

sigStr : Signal -> String
sigStr s =
  case lookup s sigName of
    Just n  => "\{show s.sig} (\{n})"
    Nothing => "\{show s.sig}"

export
prettyStatus : (pre : String) -> ProcStatus -> String
prettyStatus pre s =
  pre ++ case s of
    Exited m      => "child exited, status = \{show m}"
    Signaled s cd => "child killed by signal \{sigStr s}\{cdStr cd}"
    Stopped s     => "child stopped by signal \{sigStr s}"
    Continued     => "child continued"
    Other i       => "what happened here!? (status = \{show i})"
