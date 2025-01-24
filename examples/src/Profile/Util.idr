module Profile.Util

%default total

export
prettyNS : Integer -> String
prettyNS n = "\{secs}\{msecs}\{usecs}\{nsecs}"
  where
    secs, msecs, usecs, nsecs : String
    secs =
      case n `div` 1_000_000_000 of
        0 => ""
        s => "\{show s} s "

    msecs =
      case n `div` 1_000_000 of
        0 => ""
        s => "\{show $ s `mod` 1000} ms "

    usecs =
      case n `div` 1_000 of
        s => "\{show $ s `mod` 1000} us "

    nsecs = "\{show $ n `mod` 1000} ns"
