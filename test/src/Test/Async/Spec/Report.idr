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
  | Summary
  | Title Nat
  | DiffRemoved
  | DiffAdded
  | NoMarkup

%runElab derive "Markup" [Show,Eq,Ord]

color : Color -> List SGR
color c = [SetForeground c]

toAnsi : Markup -> List SGR
toAnsi Summary      = color Blue
toAnsi (Title 0)    = color Blue
toAnsi (Title _)    = color BrightBlue
toAnsi DiffAdded    = color Green
toAnsi DiffRemoved  = color Red
toAnsi FailedIcon   = color BrightRed
toAnsi FailedText   = color BrightRed
toAnsi SuccessIcon  = color Green
toAnsi SuccessText  = color Green
toAnsi NoMarkup     = []

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
    putStr $ renderDoc $
      indent (dpt * 2) doc

  export
  fail : (desc : String) -> Maybe Diff -> String -> IO ()
  fail desc md msg = Prelude.do
    addFailure
    addTest
    printDoc . vsep $
      [ icon FailedIcon '✗' (markup FailedText (vsep $ textLines desc))
      , indent 2 $ vsep $
          map (markup FailedText) (textLines msg) ++ maybe [] diff md
      ]

export
succeeded : (te : TestEnv) => (desc : String) -> IO ()
succeeded desc = do
  addTest
  printDoc $
    icon SuccessIcon '✓' (markup SuccessText (vsep $ textLines desc))

export
report : (te : TestEnv) => (desc : String) -> TestResult -> IO ()
report desc (Failure md msg) = fail desc md msg
report desc Success          = succeeded desc

export
summary : (te : TestEnv) => (ts,fs : Nat) -> IO ()
summary ts 0 = printDoc $ markup Summary (line "\{testCount ts} passed")
summary ts n =
  printDoc $ markup FailedText (line "\{show n} of \{testCount ts} failed")

export
printName : (te : TestEnv) => String -> IO ()
printName str = do
  n <- readIORef te.depth
  printDoc . markup (Title n) . vsep $ textLines str
