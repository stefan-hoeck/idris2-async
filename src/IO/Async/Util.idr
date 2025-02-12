module IO.Async.Util

import Data.Array
import Data.Array.Mutable
import Data.Maybe
import IO.Async.Deferred
import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Token
import IO.Async.Loop.Sync
import IO.Async.Loop.TimerH
import IO.Async.Semaphore
import IO.Async.Type
import System.Clock

%default total

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

public export
0 Handler : Type -> Type -> Type -> Type
Handler a e x = x -> Async e [] a

||| Inject an `IO (Either e a)` computation into an `Async` monad dealing
||| with several possible errors.
export
injectIO : Has x es => IO (Either x a) -> Async e es a
injectIO = sync . map (mapFst inject)

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
racePair x y =
  uncancelable $ \poll => do
    f1 <- start x
    f2 <- start y
    flip onCancel (cancel f1 >> cancel f2) $ poll $ primAsync $ \cb,t =>
      let c1 # t := f1.observe_ (\o1 => cb $ Right $ Left (o1,f2)) t
          c2 # t := f2.observe_ (\o2 => cb $ Right $ Right (f1,o2)) t
       in (\t => let _ # t := c1 t in c2 t) # t

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

||| Races the evaluation of several fibers, returning the result
||| of the winnner. The other fibers are canceled as soon as one of the
||| fibers produced an outcome.
||| case of cancelation.
||| 
||| The semantics of [[race]] are described by the following rules:
||| 
|||   1. If the winner completes with [[Outcome.Succeeded]], the race returns the successful
|||      value. The loser is canceled before returning.
|||   2. If the winner completes with [[Outcome.Errored]], the race raises the error.
|||      The loser is canceled before returning.
|||   3. If the winner completes with [[Outcome.Canceled]], the race cancels
|||      the loser and returns its result, fires an error, or returns `Nothing`
|||      its outcome is `Canceled`.
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
      Canceled      => cancel f >> join f >>= \case
        Succeeded res => pure $ Just (Right res)
        Error err     => fail err
        Canceled      => pure Nothing
    Right (f,oc) => case oc of
      Succeeded res => cancel f $> Just (Right res)
      Error err     => cancel f >> fail err
      Canceled      => cancel f >> join f >>= \case
        Succeeded res => pure $ Just (Left res)
        Error err     => fail err
        Canceled      => pure Nothing

||| This generalizes `race2` to an arbitrary heterogeneous list.
export
hrace : All (Async e es) ts -> Async e es (Maybe $ HSum ts)
hrace []       = pure Nothing
hrace [x]      = map (Just . Here) x
hrace (x :: y) =
  flip map (race2 x $ hrace y) $ \case
    Just (Left z)         => Just (Here z)
    Just (Right (Just z)) => Just (There z)
    _                     => Nothing

||| A more efficient, monomorphic version of `hrace` with slightly
||| different semantics: The winner decides the outcome of the are
||| even if it has been cancele.
export
race : List (Async e es a) -> Async e es (Maybe a)
race []  = pure Nothing
race [x] = map Just x
race xs  =
  uncancelable $ \poll => do
    def <- deferredOf (Outcome es a)
    fs  <- traverse (\f => start $ guaranteeCase f (put def)) xs
    flip guarantee (traverse_ cancel fs) $ poll (await def) >>= \case
      Succeeded res => pure (Just res)
      Error err     => fail err
      Canceled      => pure Nothing

||| Runs several non-productive fibers in parallel, terminating
||| as soon as the first one completes.
export %inline
race_ : List (Async e es ()) -> Async e es ()
race_ = ignore . race

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

||| Runs the given heterogeneous list of asynchronous computations
||| in parallel, collecting the results again in a heterogeneous list.
export
par : All (Async e es) ts -> Async e es (Maybe $ HList ts)
par []     = pure (Just [])
par [x]    = map (\v => Just [v]) x
par (h::t) =
  flip map (both h $ par t) $ \case
    Just (h2,Just t2) => Just (h2::t2)
    _                 => Nothing

parstart :
     SnocList (Fiber es a)
  -> IOArray n (Outcome es a) 
  -> Semaphore
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> List (Async e es a)
  -> Async e es (List $ Fiber es a)
parstart sx arr sem (S k) (x::xs) = do
  fib <- start $ guaranteeCase x $ \case
    Canceled => releaseAll sem
    o        => runIO (setNat arr k o) >> release sem 
  parstart (sx:<fib) arr sem k xs
parstart sx arr sem _ _ = pure (sx <>> [])

collect :
     SnocList a
  -> IOArray n (Outcome es a)
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> Bool
  -> IO1 (Outcome es $ List a)
collect sx arr 0     b t =
  if b then Succeeded (sx <>> []) # t else Canceled # t
collect sx arr (S k) b t =
  case getNat arr k t of
    Succeeded v # t => collect (sx:<v) arr k b t
    Error x # t     => Error x # t
    Canceled # t    => collect sx arr k False t

marr : HasIO io => (n : Nat) -> io (k ** IOArray k (Outcome es a))
marr n = do
  arr <- newIOArray n Canceled
  pure (n ** arr)

||| Runs the given list of computations in parallel.
|||
||| This fails with an error, as soon as the first computation
||| fails, and it returns `Nothing` as soon as the first computation
||| is canceled.
export
parseq : List (Async e es a) -> Async e es (Maybe $ List a)
parseq xs =
  uncancelable $ \poll => do
    (n ** arr) <- marr (length xs)
    sem        <- semaphore n
    fs         <- parstart [<] arr sem n xs
    flip guarantee (traverse_ cancel fs) $ poll $ do
      await sem
      runIO (collect [<] arr n True) >>= \case
        Succeeded vs => pure (Just vs)
        Error  x     => fail x
        Canceled     => pure Nothing

||| Traverses a list of values effectfully in parallel.
|||
||| This returns `Nothing` if one of the fibers was canceled.
export %inline
parTraverse : (a -> Async e es b) -> List a -> Async e es (Maybe $ List b)
parTraverse f = parseq . map f

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
  sleep : (dur : Clock Duration) -> Async e es ()
  sleep dur = do
    ev <- env
    primAsync $ \cb => primWait ev dur $ \case
      Right _ => cb (Right ())
      Left  x => cb (Left $ inject x)

  ||| Delay a computation by the given number of nanoseconds.
  export
  waitTill : Clock Monotonic -> Async e es ()
  waitTill cl = do
    now <- liftIO (clockTime Monotonic)
    sleep (timeDifference cl now)

  ||| Delay a computation by the given number of nanoseconds.
  export
  delay : (dur : Clock Duration) -> Async e es a -> Async e es a
  delay dur act = sleep dur >> act

||| Converts a number to nanoseconds
export %inline
(.ns) : Nat -> Clock Duration
n.ns = fromNano (cast n)

||| Converts a number of microseconds to nanoseconds
export %inline
(.us) : Nat -> Clock Duration
n.us = (n * 1_000).ns

||| Converts a number of seconds to nanoseconds
export %inline
(.s) : Nat -> Clock Duration
n.s = (n * 1_000_000).us

||| Converts a number of milliseconds to nanoseconds
export %inline
(.ms) : Nat -> Clock Duration
n.ms = (n * 1000).us

||| Runs an IO action, returning the time delta it took to run.
export %inline
delta : HasIO io => io () -> io (Clock Duration)
delta act = do
  c1 <- liftIO $ clockTime Monotonic
  act
  c2 <- liftIO $ clockTime Monotonic
  pure (timeDifference c2 c1)

--------------------------------------------------------------------------------
-- Running `Async`
--------------------------------------------------------------------------------

export covering
syncApp : Async SyncST [] () -> IO ()
syncApp as = do
  el  <- sync
  tg  <- newTokenGen
  runAsync 1024 el as
