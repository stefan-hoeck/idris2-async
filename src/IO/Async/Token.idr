module IO.Async.Token

import IO.Async.MVar
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
  var : MVar Nat

export
newTokenGen : IO TokenGen
newTokenGen = TG <$> newMVar 0

||| Generates a new unique fiber token.
export
token : HasIO io => (g : TokenGen) => io Token
token = liftIO $ evalState g.var (\x => (S x, T x))
