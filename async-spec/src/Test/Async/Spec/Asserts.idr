module Test.Async.Spec.Asserts

import Data.Linear.Ref1
import Data.String
import IO.Async
import Test.Async.Spec.Report
import Test.Async.Spec.TestEnv
import Test.Async.Spec.TestResult
import Text.Show.Diff
import Text.Show.Pretty

%default total

export %inline
failWith : Maybe Diff -> String -> Test e
failWith diff msg = pure $ Failure diff msg

||| Fails with an error that shows the difference between two values.
export
failDiff : Show a => Show b => a -> b -> Test e
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
diff : Show a => Show b => a -> (a -> b -> Bool) -> b -> Test e
diff x op y = if x `op` y then pure Success else failDiff x y

export infix 6 ===, =!=

||| Fails the test if the two arguments provided are not equal.
export %inline
(===) : Eq a => Show a => a -> a -> Test e
(===) x y = diff x (==) y

export
assert :
     {auto all   : All Interpolation es}
  -> {auto showa : Show a}
  -> {auto eqa   : Eq a}
  -> Async e es a
  -> (expected : a)
  -> Test e
assert as exp = do
  f <- start as
  join f >>= \case
    Succeeded res => res === exp
    Error err     =>
     let msg := collapse' $ hzipWith (\_ => interpolate) all err
      in failWith Nothing "Computation failed with error \{msg}"
    Canceled      =>
      failWith Nothing "Computation was canceled unexpectedly"

||| Operator version of `assert`
export %inline
(=!=) :
     {auto all   : All Interpolation es}
  -> {auto showa : Show a}
  -> {auto eqa   : Eq a}
  -> Async e es a
  -> (expected : a)
  -> Test e
(=!=) = assert
