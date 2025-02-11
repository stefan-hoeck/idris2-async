module IO.Async.HErr

import Data.Linear.Token
import IO.Async.Outcome
import System.Posix.Errno

%default total

||| A monad with error handling via a generalized bind
|||
||| Possible errors are given as a `List Type` parameter, and a single
||| error is wrapped in an `HSum`.
public export
interface Monad (m es) => HErr (0 m : List Type -> Type -> Type) where
  fail         : HSum es -> m es a
  handleErrors : (HSum es -> m fs a) -> m es a -> m fs a

||| Lifts a value into `Async`.
export %inline
succeed : HErr m => a -> m es a
succeed = pure

export %inline
fromResult : HErr m => Result es a -> m es a
fromResult = either fail pure

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

||| Throws a single error by injecting it into the sum of possible errors.
export %inline
throw : HErr m => Has x es => x -> m es a
throw = fail . inject

||| Inject an `Either e a` computation into an `Async` monad dealing
||| with several possible errors.
export
injectEither : HErr m => Has x es => Either x a -> m es a
injectEither (Left v)  = throw v
injectEither (Right v) = succeed v

export %inline
mapErrors : HErr m => (HSum es -> HSum fs) -> m es a -> m fs a
mapErrors f = handleErrors (fail . f)

export %inline
weakenErrors : HErr m => m [] a -> m fs a
weakenErrors = handleErrors absurd

export %inline
dropErrs : HErr m => m es () -> m [] ()
dropErrs = handleErrors (const $ succeed ())

export %inline
liftErrors : HErr m => m es a -> m fs (Result es a)
liftErrors = handleErrors (succeed . Left) . map Right

export %inline
liftError : HErr m => m [e] a -> m fs (Either e a)
liftError = handleErrors (pure . Left . project1) . map Right

export %inline
handle : HErr m => All (\e => e -> m [] a) es -> m es a -> m [] a
handle hs = handleErrors (collapse' . hzipWith id hs)

export
injectIO : HErr m => HasIO (m es) => IO (Result es a) -> m es a
injectIO act = liftIO act >>= either fail pure

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

export
HErr (Either . HSum) where
  fail = Left
  handleErrors f (Right v) = Right v
  handleErrors f (Left x)  = f x

export
HErr Outcome where
  fail = Error
  handleErrors f (Error x)     = f x
  handleErrors f (Succeeded v) = Succeeded v
  handleErrors f Canceled      = Canceled

eoi : Has Errno es => EPrim a -> IO (Result es a)
eoi act =
  runIO $ \t => case act t of
      R r t => Right r # t
      E x t => Left (inject x) # t

export %inline
HErr m => HasIO (m es) => Has Errno es => ErrIO (m es) where
  eprim act = injectIO (eoi act)
