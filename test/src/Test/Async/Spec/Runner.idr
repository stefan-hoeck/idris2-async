module Test.Async.Spec.Runner

import Data.IORef
import Data.String
import Test.Async.Spec.Report
import Test.Async.Spec.TestEnv
import Test.Async.Spec.TestResult
import System

%default total

toBool : Maybe String -> Bool
toBool Nothing  = False
toBool (Just s) =
  case toLower s of
    "1"    => True
    "yes"  => True
    "true" => True
    _      => False

covering
run : TestEnv => TestTree -> IO ()
run (Leaf desc x)  = printDesc desc >> x >>= report
run (Node name xs) = do
  printName name 
  incDepth
  traverse_ run xs
  decDepth

export covering
test : TestTree -> IO ()
test tree = do
  b  <- toBool <$> getEnv "SPEC_COLOR"
  te <- mkEnv b
  run @{te} tree
  ts <- readIORef te.tests
  fs <- readIORef te.failures
  summary ts fs
  if fs > 0
     then exitFailure
     else exitSuccess


