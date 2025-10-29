module Test.Async.Spec.TestEnv

import Data.Linear.Ref1
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
mkEnv : Lift1 World f => Bool -> f TestEnv
mkEnv b = do
  d <- newref Z
  f <- newref Z
  t <- newref Z
  pure $ TE d f t b LL80

parameters {auto te  : TestEnv}
           {auto has : HasIO io}

  export %inline
  addFailure : io ()
  addFailure = runIO $ casmod1 te.failures S

  export %inline
  addTest : io ()
  addTest = runIO $ casmod1 te.tests S

  export %inline
  incDepth : io ()
  incDepth = runIO $ casmod1 te.depth S
  
  export %inline
  decDepth : io ()
  decDepth = runIO $ casmod1 te.depth pred

export
renderDoc : (te : TestEnv) => Doc te.layout -> String
renderDoc = render te.layout . indent 2
