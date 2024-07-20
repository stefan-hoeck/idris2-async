module Test.Async.Spec.TestResult

import Derive.Prelude
import Text.Show.Diff

%language ElabReflection
%default total

||| The difference between some expected and actual value.
public export
record Diff where
  constructor MkDiff
  diffPrefix  : String
  diffRemoved : String
  diffInfix   : String
  diffAdded   : String
  diffSuffix  : String
  diffValue   : ValueDiff

%runElab derive "TestResult.Diff" [Show,Eq]

public export
data TestResult : Type where
  Failure : Maybe Diff -> String -> TestResult
  Success : TestResult

%runElab derive "TestResult" [Show,Eq]

public export
0 Test : Type
Test = IO TestResult

public export
data TestTree : Type where
  Node : (name : String) -> List TestTree -> TestTree
  Leaf : (desc : String) -> Test -> TestTree
