module Test.Async.Spec.Report

import Data.IORef
import Data.String
import Derive.Prelude
import Test.Async.Spec.TestEnv
import Test.Async.Spec.TestResult
import Text.PrettyPrint.Bernardy.ANSI
import Text.Show.Diff

%language ElabReflection
%default total

public export
data Markup =
    FailedIcon
  | FailedText
  | SuccessIcon
  | SuccessText
  | AnnotationValue
  | DiffRemoved
  | DiffAdded
  | NoMarkup

%runElab derive "Markup" [Show,Eq,Ord]

color : Color -> List SGR
color c = [SetForeground c]

toAnsi : Markup -> List SGR
toAnsi AnnotationValue = color Magenta
toAnsi DiffAdded       = color Green
toAnsi DiffRemoved     = color Red
toAnsi FailedIcon      = color BrightRed
toAnsi FailedText      = color BrightRed
toAnsi SuccessIcon     = color Green
toAnsi SuccessText     = color Green
toAnsi NoMarkup        = []

testCount : Nat -> String
testCount 1 = "1 test"
testCount n = "\{show n} tests"

parameters {auto te : TestEnv}

  markup : Markup -> Doc te.layout -> Doc te.layout
  markup m d = case te.useColor of
    False => d
    True  => decorate (toAnsi m) d

  %inline markupLine : Markup -> String -> Doc te.layout
  markupLine m = markup m . line

  icon : Markup -> Char -> Doc te.layout -> Doc te.layout
  icon m i x = markup m (symbol i) <++> x

  lineDiff : LineDiff -> Doc te.layout
  lineDiff (LineSame x)    = "  " <+> pretty x
  lineDiff (LineRemoved x) = markup DiffRemoved $ "- " <+> pretty x
  lineDiff (LineAdded x)   = markup DiffAdded   $ "+ " <+> pretty x

  diff : Diff -> List (Doc te.layout)
  diff (MkDiff pre removed inf added suffix df) =
    ( markup NoMarkup    (line pre)     <+>
      markup DiffRemoved (line removed) <+>
      markup NoMarkup    (line inf)     <+>
      markup DiffAdded   (line added)   <+>
      markup NoMarkup    (line suffix)
    ) :: map lineDiff (toLineDiff df)

  textLines : String -> List (Doc te.layout)
  textLines = map line . lines

  printDoc : Doc te.layout -> IO ()
  printDoc doc = do
    dpt <- readIORef te.depth
    putStrLn $ renderDoc $
      indent (dpt * 2) doc

export
fail : (te : TestEnv) => Maybe Diff -> String -> IO ()
fail md msg = Prelude.do
  addFailure
  addTest
  printDoc $ vsep (textLines msg ++ maybe [] diff md)

export
succeeded : (te : TestEnv) => String -> IO ()
succeeded msg = do
  addTest
  printDoc (line msg)

export
report : (te : TestEnv) => TestResult -> IO ()
report (Failure md msg) = fail md msg
report Success          = succeeded "passed"

export
summary : (te : TestEnv) => (ts,fs : Nat) -> IO ()
summary ts 0 = putStrLn "\{testCount ts} passed"
summary ts n = putStrLn "\{show n} of \{testCount ts} failed"

export
printName : (te : TestEnv) => String -> IO ()
printName str = printDoc $ vsep (textLines str)

export
printDesc : (te : TestEnv) => String -> IO ()
printDesc str = printDoc $ vsep (textLines str)
