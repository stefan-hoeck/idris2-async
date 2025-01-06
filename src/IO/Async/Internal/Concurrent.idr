||| Concurrency primitives in `PrimIO`
module IO.Async.Internal.Concurrent

import Data.Array
import IO.Async.Loop

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
withLock : Mutex -> IO1 b -> IO1 b
withLock m f t =
  let _  # t := toF1 (acqMutex m) t
      vb # t := f t
      _  # t := toF1 (relMutex m) t
   in vb # t

export %inline
withLockAt : IArray n Mutex -> Fin n -> IO1 b -> IO1 b
withLockAt ms x = withLock (ms `at` x)

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
