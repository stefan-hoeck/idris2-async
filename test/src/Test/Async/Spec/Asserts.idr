module Test.Async.Spec.Asserts

import Data.IORef
import Data.String
import IO.Async
import IO.Async.Loop.Sync
import Test.Async.Spec.Report
import Test.Async.Spec.TestEnv
import Test.Async.Spec.TestResult
import Text.Show.Diff
import Text.Show.Pretty

%default total

export covering
runAsyncBlocking : Async SyncST es a -> IO (Outcome es a)
runAsyncBlocking as = do
  ref <- newIORef (the (Outcome es a) Canceled)
  syncApp (dropErrs $ ignore $ guaranteeCase as (writeIORef ref))
  readIORef ref

export %inline
failWith : Maybe Diff -> String -> Test
failWith diff msg = pure $ Failure diff msg

||| Fails with an error that shows the difference between two values.
export
failDiff : Show a => Show b => a -> b -> Test
failDiff x y =
  case valueDiff <$> reify x <*> reify y of
    Nothing =>
      failWith Nothing $
        unlines
          [ "Failed"
          , "━━ lhs ━━"
          , ppShow x
          , "━━ rhs ━━"
          , ppShow y
          ]

    Just vdiff@(Same _) =>
      failWith
        (Just $ MkDiff "━━━ Failed ("  "" "no differences" "" ") ━━━" vdiff)
        ""

    Just vdiff =>
      failWith
        (Just $ MkDiff "━━━ Failed (" "- lhs" ") (" "+ rhs" ") ━━━" vdiff)
        ""

export %inline
diff : Show a => Show b => a -> (a -> b -> Bool) -> b -> Test
diff x op y = if x `op` y then pure Success else failDiff x y

export infix 6 ===

||| Fails the test if the two arguments provided are not equal.
export %inline
(===) : Eq a => Show a => a -> a -> Test
(===) x y = diff x (==) y

export covering
assert : Show a => Eq a => Async SyncST [] a -> (expected : a) -> IO TestResult
assert as exp = do
  runAsyncBlocking as >>= \case
    Error err     => absurd err
    Canceled      => failWith Nothing "Computation was canceled unexpectedly"
    Succeeded res => res === exp
