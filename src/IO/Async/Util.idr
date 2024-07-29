module IO.Async.Util

import Data.Maybe
import IO.Async.Type
import IO.Async.Internal.Concurrent
import IO.Async.Internal.ExecutionContext
import IO.Async.Internal.Ref
import IO.Async.Internal.ThreadPool
import IO.Async.Internal.Token
import System

%default total

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

public export
0 Handler : Type -> Type -> Type
Handler a x = x -> Async [] a

||| Throws a single error by injecting it into the sum of possible errors.
export %inline
throw : Has e es => e -> Async es a
throw = fail . inject

||| Inject an `Either e a` computation into an `Async` monad dealing
||| with several possible errors.
export
injectEither : Has e es => Either e a -> Async es a
injectEither (Left v)  = throw v
injectEither (Right v) = succeed v

||| Inject an `IO (Either e a)` computation into an `Async` monad dealing
||| with several possible errors.
export
injectIO : Has e es => IO (Either e a) -> Async es a
injectIO = sync . map (mapFst inject)

export
handleErrors : (HSum es -> Async fs a) -> Async es a -> Async fs a
handleErrors f x = bind x $ either f succeed

export %inline
mapErrors : (HSum es -> HSum fs) -> Async es a -> Async fs a
mapErrors f = handleErrors (fail . f)

export %inline
weakenErrors : Async [] a -> Async fs a
weakenErrors = believe_me -- for performance and cancelation reasons

export %inline
dropErrs : Async es () -> Async [] ()
dropErrs = handleErrors (const $ succeed ())

export %inline
handle : All (Handler a) es -> Async es a -> Async [] a
handle hs = handleErrors (collapse' . hzipWith id hs)

export %inline
liftErrors : Async es a -> Async fs (Result es a)
liftErrors = handleErrors (succeed . Left) . map Right

export %inline
liftError : Async [e] a -> Async fs (Either e a)
liftError = handleErrors (pure . Left . project1) . map Right

export
embed : (onCancel : Lazy (Async es a)) ->  Outcome es a -> Async es a
embed _  (Succeeded res) = succeed res
embed _  (Error err)     = fail err
embed oc Canceled        = oc

--------------------------------------------------------------------------------
-- Handling fibers
--------------------------------------------------------------------------------

||| Semantically blocks the current fiber until the given fiber
||| produces and outcome, and returns the outcome produced.
export %inline
join : Fiber es a -> Async fs (Outcome es a)
join f = primAsync $ \cb => f.observe_ $ cb . Right

||| Cancels the given fiber.
|||
||| This will semantically block the current fiber, until the target has
||| completed.
export
cancel : (target : Fiber es a) -> Async fs ()
cancel f = uncancelable $ \_ => primIO f.cancel_ >> ignore (join f)

||| Specifies an effect that is always invoked after evaluation of
||| `fa` completes, but depends on the outcome.
export
guaranteeCase : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
guaranteeCase fa fin =
  uncancelable $ \poll =>
    let finalized := onCancel (poll fa) (fin Canceled)
     in bind finalized $ \r => weakenErrors (fin $ toOutcome r) >> terminal r

||| Specifies an effect that is always invoked after evaluation of `fa`
||| completes, regardless of the outcome.
export %inline
guarantee : Async es a -> Async [] () -> Async es a
guarantee fa = guaranteeCase fa . const

||| A pattern for safely interacting with effectful lifecycles.
||| 
||| If `acquire` completes successfully, `use` is called. If `use` succeeds, fails, or is
||| canceled, `release` is guaranteed to be called exactly once.
||| 
||| If `use` succeeds the returned value `B` is returned. If `use` returns an exception, the
||| exception is returned.
||| 
||| `acquire` is uncancelable by default, but can be unmasked. `release` is uncancelable. `use`
||| is cancelable by default, but can be masked.
export
bracketFull :
     (acquire : Poll -> Async es a)
  -> (use     : a -> Async es b)
  -> (release : a -> Outcome es b -> Async [] ())
  -> Async es b
bracketFull acquire use release =
  uncancelable $ \poll => do
    v <- acquire poll
    guaranteeCase (poll $ use v) (release v)

||| A pattern for safely interacting with effectful lifecycles.
||| 
||| If `acquire` completes successfully, `use` is called. If `use` succeeds, fails, or is
||| canceled, `release` is guaranteed to be called exactly once.
||| 
||| `acquire` is uncancelable. `release` is uncancelable. `use` is cancelable by default, but
||| can be masked.
export %inline
bracketCase :
     (acquire : Async es a)
  -> (use     : a -> Async es b)
  -> (release : a -> Outcome es b -> Async [] ())
  -> Async es b
bracketCase = bracketFull . const

||| A pattern for safely interacting with effectful lifecycles.
||| 
||| If `acquire` completes successfully, `use` is called. If `use` succeeds, fails, or is
||| canceled, `release` is guaranteed to be called exactly once.
||| 
||| `acquire` is uncancelable. `release` is uncancelable. `use` is cancelable by default, but
||| can be masked.
export %inline
bracket :
     (acquire : Async es a)
  -> (use     : a -> Async es b)
  -> (release : a -> Async [] ())
  -> Async es b
bracket acquire use release = bracketCase acquire use (const . release)

--------------------------------------------------------------------------------
-- Spawning Fibers
--------------------------------------------------------------------------------

||| A low-level primitive for racing the evaluation of two fibers that returns the [[Outcome]]
||| of the winner and the [[Fiber]] of the loser. The winner of the race is considered to be
||| the first fiber that completes with an outcome.
||| 
||| `racePair` is a cancelation-unsafe function; it is recommended to use the safer variants.
export
racePair :
     Async es a
  -> Async fs b
  -> Async gs (Either (Outcome es a, Fiber fs b) (Fiber es a, Outcome fs b))
racePair x y = do
    f1 <- start x
    f2 <- start y
    flip onCancel (cancel f1 >> cancel f2) $ primAsync $ \cb,w =>
      let MkIORes c1 w := f1.observe_ (\o1 => cb $ Right $ Left (o1,f2)) w
          MkIORes c2 w := f2.observe_ (\o2 => cb $ Right $ Right (f1,o2)) w
       in MkIORes (\x => let MkIORes _ x := c1 x in c2 x) w

||| Awaits the completion of the bound fiber and returns its result once it completes.
||| 
||| If the fiber completes with [[Outcome.Succeeded]], the successful value is returned. If the
||| fiber completes with [[Outcome.Errored]], the error is raised. If the fiber completes with
||| [[Outcome.Canceled]], `onCancel` is run.
export
joinWith : Fiber es a -> (onCancel: Lazy (Async es a)) ->  Async es a
joinWith f c = join f >>= embed c

||| Like `joinWith`, returning the `neutral` value of the `Monoid` in case of
||| cancelation.
export
joinWithNeutral : Monoid a => Fiber es a -> Async es a
joinWithNeutral f = joinWith f (pure neutral)

export
cancelable : (act : Async es a) -> (fin : Async [] ()) -> Async es (Maybe a)
cancelable act fin =
  uncancelable $ \poll => do
    fiber <- start act
    out   <- onCancel (poll $ join fiber) (fin >> cancel fiber)
    embed (poll $ canceled $> Nothing) (map Just out)

||| Races the evaluation of two fibers that returns the [[Outcome]] of the winner. The winner
||| of the race is considered to be the first fiber that completes with an outcome. The loser
||| of the race is canceled before returning.
||| 
||| @param fa
|||   the effect for the first racing fiber
||| @param fb
|||   the effect for the second racing fiber
||| 
||| @see
|||   [[race]] for a simpler variant that returns the successful outcome.
export
raceOutcome : Async es a -> Async fs b -> Async gs (Either (Outcome es a) (Outcome fs b))
raceOutcome fa fb =
  uncancelable $ \poll => poll (racePair fa fb) >>= \case
    Left  (oc,f) => cancel f $> Left oc
    Right (f,oc) => cancel f $> Right oc

||| Races the evaluation of two fibers that returns the result of the winner, except in the
||| case of cancelation.
||| 
||| The semantics of [[race]] are described by the following rules:
||| 
|||   1. If the winner completes with [[Outcome.Succeeded]], the race returns the successful
|||      value. The loser is canceled before returning.
|||   2. If the winner completes with [[Outcome.Errored]], the race raises the error.
|||      The loser is canceled before returning.
|||   3. If the winner completes with [[Outcome.Canceled]], the race returns the
|||      result of the loser, consistent with the first two rules.
|||   4. If both the winner and loser complete with [[Outcome.Canceled]],
|||      this returns `Nothing`
||| 
||| @param fa
|||   the effect for the first racing fiber
||| @param fb
|||   the effect for the second racing fiber
||| 
||| @see
|||   [[raceOutcome]] for a variant that returns the outcome of the winner.
export
race2 : Async es a -> Async es b -> Async es (Outcome [] $ Either a b)
race2 fa fb =
  uncancelable $ \poll => poll (racePair fa fb) >>= \case
    Left  (oc,f) => case oc of
      Succeeded res => cancel f $> Succeeded (Left res)
      Error err     => cancel f >> fail err
      Canceled      => join f >>= \case
        Succeeded res => pure $ Succeeded (Right res)
        Error err     => fail err
        Canceled      => pure Canceled
    Right (f,oc) => case oc of
      Succeeded res => cancel f $> Succeeded (Right res)
      Error err     => cancel f >> fail err
      Canceled      => join f >>= \case
        Succeeded res => pure $ Succeeded (Left res)
        Error err     => fail err
        Canceled      => pure Canceled

||| This generalizes `race2` to an arbitrary heterogeneous list.
export
race : All (Async es) ts -> Async es (Outcome [] $ HSum ts)
race []       = pure Canceled
race [x]      = map (Succeeded . Here) x
race (x :: y) =
  flip map (race2 x $ race y) $ \case
    Succeeded (Left z)              => Succeeded (Here z)
    Succeeded (Right (Succeeded z)) => Succeeded (There z)
    Succeeded (Right Canceled)      => Canceled
    Succeeded (Right (Error err)) impossible
    Canceled                        => Canceled
    Error err impossible

||| Races the evaluation of two fibers and returns the [[Outcome]] of both. If the race is
||| canceled before one or both participants complete, then then whichever ones are incomplete
||| are canceled.
||| 
||| @param fa
|||   the effect for the first racing fiber
||| @param fb
|||   the effect for the second racing fiber
||| 
||| @see
|||   [[both]] for a simpler variant that returns the results of both fibers.
||| 
export
bothOutcome : Async es a -> Async fs b -> Async gs (Outcome es a, Outcome fs b)
bothOutcome fa fb =
  uncancelable $ \poll => poll (racePair fa fb) >>= \case
    Left  (oc, f) => (oc,) <$> onCancel (poll $ join f) (cancel f)
    Right (f, oc) => (,oc) <$> onCancel (poll $ join f) (cancel f)

||| Races the evaluation of two fibers and returns the result of both.
||| 
||| The following rules describe the semantics of [[both]]:
||| 
|||   1. If the winner completes with [[Outcome.Succeeded]], the race waits for the loser to
|||      complete.
|||   2. If the winner completes with [[Outcome.Errored]], the race raises the
|||      error. The loser is canceled.
|||   3. If the winner completes with [[Outcome.Canceled]],
|||      the loser and the race are canceled as well.
|||   4. If the loser completes with
|||      [[Outcome.Succeeded]], the race returns the successful value of both fibers.
|||   5. If the
|||      loser completes with [[Outcome.Errored]], the race returns the error.
|||   6. If the loser
|||      completes with [[Outcome.Canceled]], the race is canceled.
|||   7. If the race is canceled
|||      before one or both participants complete, then whichever ones are incomplete are
|||      canceled.
||| 
||| @param fa
|||   the effect for the first racing fiber
||| @param fb
|||   the effect for the second racing fiber
||| 
||| @see
|||   [[bothOutcome]] for a variant that returns the [[Outcome]] of both fibers.
export
both : Async es a -> Async es b -> Async es (Outcome [] (a,b))
both fa fb =
  uncancelable $ \poll => poll (racePair fa fb) >>= \case
    Left  (oc, f) => case oc of
      Succeeded x => onCancel (poll $ join f) (cancel f) >>= \case
        Succeeded y => pure $ Succeeded (x,y)
        Error err   => fail err
        Canceled    => pure Canceled
      Error err     => cancel f >> fail err
      Canceled      => cancel f >> pure Canceled
    Right (f, oc) => case oc of
      Succeeded y => onCancel (poll $ join f) (cancel f) >>= \case
        Succeeded x => pure $ Succeeded (x,y)
        Error err   => fail err
        Canceled    => pure Canceled
      Error err     => cancel f >> fail err
      Canceled      => cancel f >> pure Canceled

--------------------------------------------------------------------------------
-- Running `Async`
--------------------------------------------------------------------------------

export covering
syncApp : Async [] () -> IO ()
syncApp as = do
  ec  <- sync
  tg  <- newTokenGen
  runAsync 1024 as

export covering
app : (n : Nat) -> {auto 0 p : IsSucc n} -> Async [] () -> IO ()
app n act = do
  tp <- mkThreadPool n
  m  <- primIO mkMutex
  c  <- primIO makeCondition
  tg <- newTokenGen
  runAsyncWith @{ec tp} 1024 act (\_ => primIO $ conditionBroadcast c)
  primIO $ acqMutex m
  primIO $ conditionWait c m
  stop tp
  usleep 100
