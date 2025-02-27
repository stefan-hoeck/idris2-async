module IO.Async.Unique

import Data.Linear.Ref1
import Derive.Prelude

%default total
%language ElabReflection

||| A unique identifier for fibers.
export
record Token where
  constructor T
  value : Nat

%runElab derive "Token" [Show,Eq,Ord]

||| Returns the internal natural number of a `Token`.
|||
||| Note: This is an implementation detail mainly used for testing.
|||       Consider `Token`s to be opaque values with an `Eq` and
|||       `Ord` implementation. Nothing else.
export %inline
tokenVal : Token -> Nat
tokenVal = value

-- Internal mutable token state. This is read and updated
-- via `casupdate1`, which is thread-safe, but currently works
-- only on Chez and JavaScript (and, possibly, Racket).
%noinline
tok_ : IORef Nat
tok_ = unsafePerformIO $ newref 0

||| Generates a new unique token.
|||
||| This token is unique throughout the lifetime of an application,
||| as it is generated from a single, global, mutable reference.
||| Unique token generation is thread-safe.
export %inline
token1 : IO1 Token
token1 = casupdate1 tok_ (\n => (n+1, T n))

||| Generates a new unique token.
|||
||| This token is unique throughout the lifetime of an application,
||| as it is generated from a single, global, mutable reference.
||| Unique token generation is thread-safe.
export %inline
token : Lift1 World f => f Token
token = lift1 token1
