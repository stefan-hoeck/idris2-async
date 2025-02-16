||| A unique token to identify fibers
module IO.Async.Internal.Token

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Ref
import Derive.Prelude

%default total
%language ElabReflection

||| A unique identifier for fibers.
export
record Token where
  constructor T
  value : Nat

%runElab derive "Token" [Show,Eq,Ord]

||| A generator for unique tokens.
export
record TokenGen where
  [noHints]
  constructor TG
  var : IORef Nat

export
newTokenGen : IO TokenGen
newTokenGen = [| TG (newref 0) |]

||| Generates a new unique fiber token.
export %inline
token : (g : TokenGen) => IO1 Token
token = casupdate1 g.var (\n => (n+1, T n))
