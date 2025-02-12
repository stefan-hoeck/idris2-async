module IO.Async.MErr

import Data.Linear.Token
import IO.Async.Outcome
import System.Posix.Errno

%default total

||| A monad with error handling via a generalized bind
|||
||| Possible errors are given as a `List Type` parameter, and a single
||| error is wrapped in an `HSum`.
public export
interface Monad (m es) => MErr (0 m : List Type -> Type -> Type) where
  fail    : HSum es -> m es a
  attempt : m es a -> m fs (Result es a)

||| Lifts a value into `Async`.
export %inline
succeed : MErr m => a -> m es a
succeed = pure

export %inline
fromResult : MErr m => Result es a -> m es a
fromResult = either fail pure

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

||| Throws a single error by injecting it into the sum of possible errors.
export %inline
throw : MErr m => Has x es => x -> m es a
throw = fail . inject

||| Inject an `Either e a` computation into an `Async` monad dealing
||| with several possible errors.
export
injectEither : MErr m => Has x es => Either x a -> m es a
injectEither (Left v)  = throw v
injectEither (Right v) = succeed v

||| Handle possible errors with the given function
export
handleErrors : MErr m => (HSum es -> m fs a) -> m es a -> m fs a
handleErrors f act = attempt act >>= either f pure

export %inline
mapErrors : MErr m => (HSum es -> HSum fs) -> m es a -> m fs a
mapErrors f = handleErrors (fail . f)

export %inline
weakenErrors : MErr m => m [] a -> m fs a
weakenErrors = handleErrors absurd

export %inline
dropErrs : MErr m => m es () -> m [] ()
dropErrs = handleErrors (const $ succeed ())

export %inline
liftErrors : MErr m => m es a -> m fs (Result es a)
liftErrors = handleErrors (succeed . Left) . map Right

export %inline
liftError : MErr m => m [e] a -> m fs (Either e a)
liftError = handleErrors (pure . Left . project1) . map Right

export %inline
handle : MErr m => All (\e => e -> m [] a) es -> m es a -> m [] a
handle hs = handleErrors (collapse' . hzipWith id hs)

||| Sequencing of computations plus error handling
export %inline
bindResult : MErr m => m es a -> (Result es a -> m fs b) -> m fs b
bindResult act f = attempt act >>= f

||| Runs the given handler in case of an error but does not
||| catch the error in question.
export %inline
onError : MErr m => m es a -> (HSum es -> m [] ()) -> m es a
onError act f = handleErrors (\x => weakenErrors (f x) >> fail x) act

export
injectIO : MErr m => HasIO (m es) => IO (Result es a) -> m es a
injectIO act = liftIO act >>= either fail pure

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

export
MErr (Either . HSum) where
  fail    = Left
  attempt = Right

export
MErr Outcome where
  fail = Error
  attempt (Error x)     = Succeeded (Left x)
  attempt (Succeeded v) = Succeeded (Right v)
  attempt Canceled      = Canceled

eoi : Has Errno es => EPrim a -> IO (Result es a)
eoi act =
  runIO $ \t => case act t of
      R r t => Right r # t
      E x t => Left (inject x) # t

export %inline
MErr m => HasIO (m es) => Has Errno es => ErrIO (m es) where
  eprim act = injectIO (eoi act)
