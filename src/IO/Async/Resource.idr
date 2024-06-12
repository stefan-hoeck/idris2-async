module IO.Async.Resource

import Data.List.Quantifiers.Extra
import IO.Async.Fiber

%default total

public export
interface Resource a where
  release : HasIO io => a -> io ()

export
useMany :
     {auto rs : All Resource ts}
  -> All (Async es) ts
  -> (HList ts -> Async es a)
  -> Async es a
useMany           []        f = f []
useMany @{_ :: _} (v :: vs) f =
  bracket v (\rv => useMany vs $ f . (rv::)) release

export %inline
use1 : Resource v => Async es v -> (v -> Async es a) -> Async es a
use1 x f = bracket x f release
