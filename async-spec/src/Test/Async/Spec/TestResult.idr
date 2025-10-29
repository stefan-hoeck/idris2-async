module Test.Async.Spec.TestResult

import Derive.Prelude
import IO.Async
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
0 Test : Type -> Type
Test e = Async e [] TestResult

dummy : Test e
dummy = pure Success

public export
data TestTree : Type -> Type where
  Node : (name : String) -> List (TestTree e) -> TestTree e
  Leaf : (desc : String) -> Test e -> TestTree e

public export
data Pre : Type where
  It : Pre
  Desc : String -> Pre

export %inline
FromString Pre where fromString = Desc

export %inline
it : Pre
it = It

export
record Post e where
  constructor At
  desc : String
  test : Test e

export %inline
at : String -> Test e -> Post e
at = At

export
data Verb = Should | Can | Must

export
Interpolation Verb where
  interpolate Should = "should"
  interpolate Can    = "can"
  interpolate Must   = "must"

export %inline
leaf : Verb -> Post e -> TestTree e
leaf v (At d t) = Leaf "\{v} \{d}" t

public export
record FlatSpecInstr e where
  constructor FSI
  verb : Verb
  pre  : Pre
  post : Post e

export infixr 5 `should`,`at`,`must`,`can`

public export %inline
should : (pre : Pre) -> (post : Post e) -> FlatSpecInstr e
should = FSI Should

public export %inline
must : (pre : Pre) -> (post : Post e) -> FlatSpecInstr e
must = FSI Must

public export %inline
can : (pre : Pre) -> (post : Post e) -> FlatSpecInstr e
can = FSI Can

public export
data ValidInstrs : (is : List (FlatSpecInstr e)) -> Type where
  IsValidInstrs :
       {0 e : Type}
    -> {0 v : Verb}
    -> {0 s : String}
    -> {0 p : Post e}
    -> {0 t : List (FlatSpecInstr e)}
    -> ValidInstrs (FSI v (Desc s) p :: t)

export
flatSpec :
     (title : String)
  -> (is    : List (FlatSpecInstr e))
  -> {auto 0 prf : ValidInstrs is}
  -> TestTree e
flatSpec ttl (FSI v (Desc s) p :: t) @{IsValidInstrs} =
  Node ttl (go [<] s [< leaf v p] t)

  where
    go :
         SnocList (TestTree e)
      -> String
      -> SnocList (TestTree e)
      -> List (FlatSpecInstr e)
      -> List (TestTree e)
    go sx s sy []                       = sx <>> [Node s $ sy <>> []]
    go sx s sy (FSI v It       p :: xs) = go sx s (sy :< leaf v p) xs
    go sx s sy (FSI v (Desc n) p :: xs) =
      go (sx :< Node s (sy <>> [])) n [< leaf v p] xs

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

spec1 : List (FlatSpecInstr e)
spec1 =
  [ "an empty list" `should` "have length 0" `at` dummy
  ,   it `should` "return Nothing on pop" `at` dummy
  ,   it `should` "return a value on pop after pushing it" `at` dummy
  , "a non-empty list" `should` "have length > 0" `at` dummy
  ,   it `should` "return a Just on pop" `at` dummy
  ]
