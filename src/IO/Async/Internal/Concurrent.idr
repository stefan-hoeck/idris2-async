||| Concurrency primitives in `PrimIO`
module IO.Async.Internal.Concurrent

%default total

--------------------------------------------------------------------------------
-- Mutex
--------------------------------------------------------------------------------

export
data Mutex : Type where [external]

export %foreign "scheme:blodwen-make-mutex"
mkMutex : PrimIO Mutex

export %foreign "scheme:blodwen-mutex-acquire"
acqMutex : Mutex -> PrimIO ()

export %foreign "scheme:blodwen-mutex-release"
relMutex : Mutex -> PrimIO ()

export %inline
withMutex : Mutex -> PrimIO b -> PrimIO b
withMutex m f w =
  let MkIORes _  w := acqMutex m w
      MkIORes vb w := f w
      MkIORes _  w := relMutex m w
   in MkIORes vb w

--------------------------------------------------------------------------------
-- Condition
--------------------------------------------------------------------------------

export
data Condition : Type where [external]

export %foreign "scheme,racket:blodwen-make-cv"
                "scheme,chez:blodwen-make-condition"
makeCondition : PrimIO Condition

export %foreign "scheme,racket:blodwen-cv-wait"
                "scheme,chez:blodwen-condition-wait"
conditionWait : Condition -> Mutex -> PrimIO ()

export %foreign "scheme,chez:blodwen-condition-wait-timeout"
conditionWaitTimeout : Condition -> Mutex -> Integer -> PrimIO ()

export %foreign "scheme,racket:blodwen-cv-signal"
                "scheme,chez:blodwen-condition-signal"
conditionSignal : Condition -> PrimIO ()

export %foreign "scheme,racket:blodwen-cv-broadcast"
                "scheme,chez:blodwen-condition-broadcast"
conditionBroadcast : Condition -> PrimIO ()
