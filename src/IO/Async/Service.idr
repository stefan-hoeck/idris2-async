module IO.Async.Service

import Data.Linear.Deferred
import IO.Async
import IO.Async.Channel

%default total

--------------------------------------------------------------------------------
-- Service
--------------------------------------------------------------------------------

||| A `Service` describes an asynchronous, effectful convertion from
||| "requests" to (dependently typed) "responses" with the potential
||| of failing with one of the given error types.
|||
||| A `Service` is a resource that should be properly released once it
||| is no longer needed.
public export
record Service (e : Type) (errs : List Type) (req : Type) (resp : req -> Type) where
  [noHints]
  constructor MkService
  close : Async e [] ()
  send  : (r : req) -> Async e errs (resp r)

export %inline
Resource (Async e) (Service e es a p) where cleanup = close

record Req (errs : List Type) (a : Type) (p : a -> Type) where
  constructor R
  req  : a
  resp : Once World (Result errs $ p req)

parameters {0 a,e    : Type}
           {default 100 capacity : Nat}
           (0 p      : a -> Type)

  ||| Sets up a stateful service that runs continuously in the background
  ||| until it is finally closed.
  export covering
  service :
       s
    -> (s -> (v : a) -> Async e es (s, p v))
    -> Async e fs (Service e es a p)
  service ini conv = do
    chnl <- channelOf (Req es a p) capacity
    fbr  <- start (go ini chnl)
    pure $ MkService (close chnl >> wait fbr) (snd chnl)
 
   where
     -- loops until the channel is closed
     go : s -> Channel (Req es a p) -> Async e [] ()
     go st chnl = do
       Just (R req o) <- receive chnl | Nothing => pure ()
       attempt (conv st req) >>= \case
         Left x        => putOnce o (Left x)  >> go st  chnl
         Right (st2,r) => putOnce o (Right r) >> go st2 chnl

     snd : Channel (Req es a p) -> (v : a) -> Async e es (p v)
     snd chnl v = do
       o <- onceOf (Result es $ p v)
       send chnl (R v o) >>= \case
         Closed => canceled >> never
         _      => awaitOnce o >>= either fail pure

  ||| Sets up a stateless service that runs continuously in the background
  ||| until it is finally closed.
  export covering
  stateless : ((v : a) -> Async e es (p v)) -> Async e fs (Service e es a p)
  stateless f = service () $ \_,v => ((),) <$> f v

  ||| Sets up a stateful service that runs continuously in the background
  ||| until it is finally closed.
  export covering
  stateful : s -> (s -> (v : a) -> (s, p v)) -> Async e fs (Service e es a p)
  stateful ini conv = service ini $ \x,st => pure $ conv x st
