module IO.Async.ExecutionContext

import Data.IORef
import Data.Queue
import IO.Async.Token

%default total

--------------------------------------------------------------------------------
-- Execution Context
--------------------------------------------------------------------------------

||| A context for submitting and running commands asynchronously.
public export
record ExecutionContext where
  [noHints]
  constructor EC
  tokenGen : TokenGen
  submit   : (spawn : Bool) -> IO () -> IO ()
  limit    : Nat

export %inline %hint
ecToTokenGen : ExecutionContext => TokenGen
ecToTokenGen @{ec} = ec.tokenGen

||| A synchronous execution context running all asynchronous computations
||| on the calling thread.
export covering
sync : IO (ExecutionContext)
sync = do
  tg <- newTokenGen
  q  <- newIORef Queue.empty
  pure $ EC tg (submitToQueue q) 1_000_000

  where
    covering
    runQueue : IORef (Queue $ IO ()) -> IO ()
    runQueue ref = do
      dequeue <$> readIORef ref >>= \case
        Nothing      => pure ()
        Just (act,q) => writeIORef ref q >> act >> runQueue ref

    covering
    submitToQueue : IORef (Queue $ IO ()) -> Bool -> IO () -> IO ()
    submitToQueue ref spawn act = do
      modifyIORef ref (`enqueue` act)
      unless spawn (runQueue ref)
