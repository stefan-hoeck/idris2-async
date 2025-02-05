module IO.Async.ErrorIO

import IO.Async.Outcome

%default total

||| A monad with error handling via a generalized bind
|||
||| Possible errors are given as a `List Type` parameter, and a single
||| error is wrapped in an `HSum`.
public export
interface ErrorIO (0 m : List Type -> Type -> Type) where
  fromResult : Result es a -> m es a
  bindResult : m es a -> (Result es a -> m fs b) -> m fs b

||| Lifts a value into `Async`.
export %inline
succeed : ErrorIO m => a -> m es a
succeed = fromResult . Right

||| Lifts an error `Result` into `Async`.
export %inline
fail : ErrorIO m => HSum es -> m es a
fail = fromResult . Left

export %inline
ErrorIO m => Functor (m es) where
  map f x = bindResult x $ fromResult . map f

export %inline
ErrorIO m => Applicative (m es) where
  pure = succeed
  fa <*> ma = bindResult fa $ either fail (<$> ma)

export %inline
ErrorIO m => Monad (m es) where
  x >>= f = bindResult x (either fail f)

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

||| Throws a single error by injecting it into the sum of possible errors.
export %inline
throw : ErrorIO m => Has x es => x -> m es a
throw = fail . inject

||| Inject an `Either e a` computation into an `Async` monad dealing
||| with several possible errors.
export
injectEither : ErrorIO m => Has x es => Either x a -> m es a
injectEither (Left v)  = throw v
injectEither (Right v) = succeed v

export
handleErrors : ErrorIO m => (HSum es -> m fs a) -> m es a -> m fs a
handleErrors f x = bindResult x $ either f succeed

export %inline
mapErrors : ErrorIO m => (HSum es -> HSum fs) -> m es a -> m fs a
mapErrors f = handleErrors (fail . f)

export %inline
weakenErrors : ErrorIO m => m [] a -> m fs a
weakenErrors = handleErrors absurd

export %inline
dropErrs : ErrorIO m => m es () -> m [] ()
dropErrs = handleErrors (const $ succeed ())

export %inline
liftErrors : ErrorIO m => m es a -> m fs (Result es a)
liftErrors = handleErrors (succeed . Left) . map Right

export %inline
liftError : ErrorIO m => m [e] a -> m fs (Either e a)
liftError = handleErrors (pure . Left . project1) . map Right

export %inline
handle : ErrorIO m => All (\e => e -> m [] a) es -> m es a -> m [] a
handle hs = handleErrors (collapse' . hzipWith id hs)
