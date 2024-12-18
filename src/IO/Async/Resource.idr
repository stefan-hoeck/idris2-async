module IO.Async.Resource

import Data.List.Quantifiers.Extra
import IO.Async.Type
import IO.Async.Util

%default total

public export
interface Resource a where
  cleanup : a -> Async e [] ()

||| Allocate a resource, use it in a program, and make sure to release it
||| afterwards.
export %inline
use1 : Resource a => Async e es a -> (a -> Async e es b) -> Async e es b
use1 alloc run = alloc >>= \r => guarantee (run r) (cleanup r)

||| Like `use1` but for a heterogeneous list of resources.
export
use : All Resource ts => All (Async e es) ts -> (HList ts -> Async e es b) -> Async e es b
use @{[]}   []     run = run []
use @{_::_} (h::t) run = use1 h (\r => use t (run . (r::)))
