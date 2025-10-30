module Test.Async.Spec.Runner

import Data.Linear.Ref1
import Data.String
import IO.Async
import System
import Test.Async.Spec.Report
import Test.Async.Spec.TestEnv
import Test.Async.Spec.TestResult

%default total

toBool : Maybe String -> Bool
toBool Nothing  = False
toBool (Just s) =
  case toLower s of
    "1"    => True
    "yes"  => True
    "true" => True
    _      => False

run : TestEnv => TestTree e -> Async e [] ()
run (Leaf desc x)  = x >>= report desc
run (Node name xs) = do
  printName name 
  incDepth
  assert_total $ traverse_ run xs
  decDepth

export
runTree : TestTree e -> Async e [] ()
runTree tree = do
  b  <- toBool <$> getEnv "SPEC_COLOR"
  te <- mkEnv b
  run @{te} tree
  ts <- readref te.tests
  fs <- readref te.failures
  summary ts fs
  when (fs > 0) exitFailure
