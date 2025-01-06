module IO.Async.Util

import Data.Maybe
import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Token
import IO.Async.Loop.Sync
import IO.Async.Loop.TimerH
import IO.Async.Type
import System.Clock

%default total

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

public export
0 Handler : Type -> Type -> Type -> Type
Handler a e x = x -> Async e [] a

||| Throws a single error by injecting it into the sum of possible errors.
export %inline
throw : Has x es => x -> Async e es a
throw = fail . inject

||| Inject an `Either e a` computation into an `Async` monad dealing
||| with several possible errors.
export
injectEither : Has x es => Either x a -> Async e es a
injectEither (Left v)  = throw v
injectEither (Right v) = succeed v

||| Inject an `IO (Either e a)` computation into an `Async` monad dealing
||| with several possible errors.
export
injectIO : Has x es => IO (Either x a) -> Async e es a
injectIO = sync . map (mapFst inject)

export
handleErrors : (HSum es -> Async e fs a) -> Async e es a -> Async e fs a
handleErrors f x = bind x $ either f succeed

export %inline
mapErrors : (HSum es -> HSum fs) -> Async e es a -> Async e fs a
mapErrors f = handleErrors (fail . f)

export %inline
weakenErrors : Async e [] a -> Async e fs a
weakenErrors = believe_me -- for performance and cancelation reasons

export %inline
dropErrs : Async e es () -> Async e [] ()
dropErrs = handleErrors (const $ succeed ())

export %inline
handle : All (Handler a e) es -> Async e es a -> Async e [] a
handle hs = handleErrors (collapse' . hzipWith id hs)

export %inline
liftErrors : Async e es a -> Async e fs (Result es a)
liftErrors = handleErrors (succeed . Left) . map Right

export %inline
liftError : Async e [e] a -> Async e fs (Either e a)
liftError = handleErrors (pure . Left . project1) . map Right

export
embed : (onCancel : Lazy (Async e es a)) ->  Outcome es a -> Async e es a
embed _  (Succeeded res) = succeed res
embed _  (Error err)     = fail err
embed oc Canceled        = oc

--------------------------------------------------------------------------------
-- Handling fibers
--------------------------------------------------------------------------------

||| Semantically blocks the current fiber until the given fiber
||| produces and outcome, and returns the outcome produced.
export %inline
join : Fiber es a -> Async e fs (Outcome es a)
join f = primAsync $ \cb => f.observe_ $ cb . Right

||| Awaits the termination of a fiber ignoring its outcome.
export %inline
wait : Fiber es a -> Async e fs ()
wait = ignore . join

||| Cancels the given fiber.
|||
||| This will semantically block the current fiber, until the target has
||| completed.
export
cancel : (target : Fiber es a) -> Async e fs ()
cancel f = uncancelable $ \_ => runIO f.cancel_ >> ignore (join f)

||| Specifies an effect that is always invoked after evaluation of
||| `fa` completes, but depends on the outcome.
export
guaranteeCase : Async e es a -> (Outcome es a -> Async e [] ()) -> Async e es a
guaranteeCase fa fin =
  uncancelable $ \poll =>
    let finalized := onCancel (poll fa) (fin Canceled)
     in bind finalized $ \r => weakenErrors (fin $ toOutcome r) >> terminal r

||| Specifies an effect that is always invoked after evaluation of `fa`
||| completes, regardless of the outcome.
export %inline
guarantee : Async e es a -> Async e [] () -> Async e es a
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
     (acquire : Poll e -> Async e es a)
  -> (use     : a -> Async e es b)
  -> (release : a -> Outcome es b -> Async e [] ())
  -> Async e es b
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
     (acquire : Async e es a)
  -> (use     : a -> Async e es b)
  -> (release : a -> Outcome es b -> Async e [] ())
  -> Async e es b
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
     (acquire : Async e es a)
  -> (use     : a -> Async e es b)
  -> (release : a -> Async e [] ())
  -> Async e es b
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
     Async e es a
  -> Async e fs b
  -> Async e gs (Either (Outcome es a, Fiber fs b) (Fiber es a, Outcome fs b))
racePair x y = do
    f1 <- start x
    f2 <- start y
    flip onCancel (cancel f1 >> cancel f2) $ primAsync $ \cb,t =>
      let c1 # t := f1.observe_ (\o1 => cb $ Right $ Left (o1,f2)) t
          c2 # t := f2.observe_ (\o2 => cb $ Right $ Right (f1,o2)) t
       in (\x => let _ # x := c1 x in c2 x) # t

||| Awaits the completion of the bound fiber and returns its result once it completes.
||| 
||| If the fiber completes with [[Outcome.Succeeded]], the successful value is returned. If the
||| fiber completes with [[Outcome.Errored]], the error is raised. If the fiber completes with
||| [[Outcome.Canceled]], `onCancel` is run.
export
joinWith : Fiber es a -> (onCancel: Lazy (Async e es a)) ->  Async e es a
joinWith f c = join f >>= embed c

||| Like `joinWith`, returning the `neutral` value of the `Monoid` in case of
||| cancelation.
export
joinWithNeutral : Monoid a => Fiber es a -> Async e es a
joinWithNeutral f = joinWith f (pure neutral)

export
cancelable : (act : Async e es a) -> (fin : Async e [] ()) -> Async e es (Maybe a)
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
raceOutcome : Async e es a -> Async e fs b -> Async e gs (Either (Outcome es a) (Outcome fs b))
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
race2 : Async e es a -> Async e es b -> Async e es (Maybe $ Either a b)
race2 fa fb =
  uncancelable $ \poll => poll (racePair fa fb) >>= \case
    Left  (oc,f) => case oc of
      Succeeded res => cancel f $> Just (Left res)
      Error err     => cancel f >> fail err
      Canceled      => join f >>= \case
        Succeeded res => pure $ Just (Right res)
        Error err     => fail err
        Canceled      => pure Nothing
    Right (f,oc) => case oc of
      Succeeded res => cancel f $> Just (Right res)
      Error err     => cancel f >> fail err
      Canceled      => join f >>= \case
        Succeeded res => pure $ Just (Left res)
        Error err     => fail err
        Canceled      => pure Nothing

||| This generalizes `race2` to an arbitrary heterogeneous list.
export
race : All (Async e es) ts -> Async e es (Maybe $ HSum ts)
race []       = pure Nothing
race [x]      = map (Just . Here) x
race (x :: y) =
  flip map (race2 x $ race y) $ \case
    Just (Left z)         => Just (Here z)
    Just (Right (Just z)) => Just (There z)
    _                     => Nothing

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
bothOutcome : Async e es a -> Async e fs b -> Async e gs (Outcome es a, Outcome fs b)
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
both : Async e es a -> Async e es b -> Async e es (Maybe (a,b))
both fa fb =
  uncancelable $ \poll => poll (racePair fa fb) >>= \case
    Left  (oc, f) => case oc of
      Succeeded x => onCancel (poll $ join f) (cancel f) >>= \case
        Succeeded y => pure $ Just (x,y)
        Error err   => fail err
        Canceled    => pure Nothing
      Error err     => cancel f >> fail err
      Canceled      => cancel f >> pure Nothing
    Right (f, oc) => case oc of
      Succeeded y => onCancel (poll $ join f) (cancel f) >>= \case
        Succeeded x => pure $ Just (x,y)
        Error err   => fail err
        Canceled    => pure Nothing
      Error err     => cancel f >> fail err
      Canceled      => cancel f >> pure Nothing

||| Runs the given heterogeneous lists of asynchronous computations
||| in parallel, collecting the results again in a heterogeneous list.
export
par : All (Async e es) ts -> Async e es (Maybe $ HList ts)
par []     = pure (Just [])
par [x]    = map (\v => Just [v]) x
par (h::t) =
  flip map (both h $ par t) $ \case
    Just (h2,Just t2) => Just (h2::t2)
    _                 => Nothing

||| Traverses a list of values effectfully in parallel.
|||
||| This returns `Nothing` if one of the fibers was canceled.
export
parTraverse : (a -> Async e es b) -> List a -> Async e es (Maybe $ List b)
parTraverse f []     = pure (Just [])
parTraverse f [x]    = map (Just . pure) (f x)
parTraverse f (h::t) =
  flip map (both (f h) (parTraverse f t)) $ \case
    Just (h2,Just t2) => Just (h2::t2)
    _                 => Nothing

--------------------------------------------------------------------------------
-- Async Utilitis
--------------------------------------------------------------------------------

||| Like `primAsync` but does not provide a hook for canceling.
export
primAsync_ : ((Result es a -> IO1 ()) -> IO1 ()) -> Async e es a
primAsync_ f =
  primAsync $ \cb,t =>
    let _ # t := f cb t
     in dummy # t

--------------------------------------------------------------------------------
-- Sleeping and Timed Execution
--------------------------------------------------------------------------------

||| Wraps a lazy value in an `Async`.
export
lazy : Lazy a -> Async e es a
lazy v = primAsync_ $ \cb => cb (Right v)

parameters {auto has : Has Errno es}
           {auto tim : TimerH e}

  ||| Delay a computation by the given number of nanoseconds.
  export
  waitTill : Clock Monotonic -> Async e es ()
  waitTill cl = do
    ev <- env
    primAsync $ \cb => primWaitTill ev cl $ \case
      Right _ => cb (Right ())
      Left  x => cb (Left $ inject x)

  ||| Delay a computation by the given number of nanoseconds.
  export
  sleep : (dur : Clock Duration) -> Async e es ()
  sleep dur = do
    now <- liftIO (clockTime Monotonic)
    waitTill (addDuration now dur)

  ||| Delay a computation by the given number of nanoseconds.
  export
  delay : (dur : Clock Duration) -> Async e es a -> Async e es a
  delay dur act = sleep dur >> act

||| Converts a number of microseconds to nanoseconds
export
(.us) : Nat -> Clock Duration
n.us = fromNano . cast $ n * 1_000

||| Converts a number of seconds to nanoseconds
export
(.s) : Nat -> Clock Duration
n.s = (n * 1_000_000).us

||| Converts a number of milliseconds to nanoseconds
export
(.ms) : Nat -> Clock Duration
n.ms = (n * 1000).us

--------------------------------------------------------------------------------
-- Running `Async`
--------------------------------------------------------------------------------

export covering
syncApp : Async SyncST [] () -> IO ()
syncApp as = do
  el  <- sync
  tg  <- newTokenGen
  runAsync 1024 el as
