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

dummy : Test
dummy = pure Success

public export
data TestTree : Type where
  Node : (name : String) -> List TestTree -> TestTree
  Leaf : (desc : String) -> Test -> TestTree

export
data Pre : Type where
  It : Pre
  Desc : String -> Pre

export %inline
FromString Pre where fromString = Desc

export %inline
it : Pre
it = It

export
record Post where
  constructor At
  desc : String
  test : Test

export %inline
at : String -> Test -> Post
at = At

export
data Verb = Should | Can | Must

export
Interpolation Verb where
  interpolate Should = "should"
  interpolate Can    = "can"
  interpolate Must   = "must"

export %inline
leaf : Verb -> Post -> TestTree
leaf v (At d t) = Leaf "\{v} \{d}" t

public export
record FlatSpecInstr where
  constructor FSI
  verb : Verb
  pre  : Pre
  post : Post

export infixr 5 `should`,`at`,`must`,`can`

public export %inline
should : (pre : Pre) -> (post : Post) -> FlatSpecInstr
should = FSI Should

public export %inline
must : (pre : Pre) -> (post : Post) -> FlatSpecInstr
must = FSI Must

public export %inline
can : (pre : Pre) -> (post : Post) -> FlatSpecInstr
can = FSI Can

public export
data ValidInstrs : (is : List FlatSpecInstr) -> Type where
  IsValidInstrs :
       {0 v : Verb}
    -> {0 s : String}
    -> {0 p : Post}
    -> {0 t : List FlatSpecInstr}
    -> ValidInstrs (FSI v (Desc s) p :: t)

export
flatSpec :
     (title : String)
  -> (is    : List FlatSpecInstr)
  -> {auto 0 prf : ValidInstrs is}
  -> TestTree
flatSpec ttl (FSI v (Desc s) p :: t) @{IsValidInstrs} =
  Node ttl (go [<] s [< leaf v p] t)

  where
    go :
         SnocList TestTree
      -> String
      -> SnocList TestTree
      -> List FlatSpecInstr
      -> List TestTree
    go sx s sy []                       = sx <>> [Node s $ sy <>> []]
    go sx s sy (FSI v It       p :: xs) = go sx s (sy :< leaf v p) xs
    go sx s sy (FSI v (Desc n) p :: xs) =
      go (sx :< Node s (sy <>> [])) n [< leaf v p] xs

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

spec1 : List FlatSpecInstr
spec1 =
  [ "an empty list" `should` "have length 0" `at` dummy
  ,   it `should` "return Nothing on pop" `at` dummy
  ,   it `should` "return a value on pop after pushing it" `at` dummy
  , "a non-empty list" `should` "have length > 0" `at` dummy
  ,   it `should` "return a Just on pop" `at` dummy
  ]
