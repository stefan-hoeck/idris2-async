module Test.Async.Spec.TestEnv

import Data.IORef
import Data.Nat
import Text.PrettyPrint.Bernardy

%default total

public export
record TestEnv where
  [noHints]
  constructor TE
  depth    : IORef Nat
  failures : IORef Nat
  tests    : IORef Nat
  useColor : Bool
  layout   : LayoutOpts

export
LL80 : LayoutOpts
LL80 = Opts 80

export
mkEnv : Bool -> IO TestEnv
mkEnv b = do
  d <- newIORef Z
  f <- newIORef Z
  t <- newIORef Z
  pure $ TE d f t b LL80

export
addFailure : (te : TestEnv) => IO ()
addFailure = modifyIORef te.failures S

export
addTest : (te : TestEnv) => IO ()
addTest = modifyIORef te.tests S

export
incDepth : (te : TestEnv) => IO ()
incDepth = modifyIORef te.depth S

export
decDepth : (te : TestEnv) => IO ()
decDepth = modifyIORef te.depth pred

export
renderDoc : (te : TestEnv) => Doc te.layout -> String
renderDoc = render te.layout . indent 2
