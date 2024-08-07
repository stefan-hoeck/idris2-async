||| A context for asynchronously schedule and execute different kinds
||| of tasks.
module IO.Async.Internal.ExecutionContext

import Data.Queue
import IO.Async.Internal.Ref
import IO.Async.Internal.Timer
import System.Clock

%default total

--------------------------------------------------------------------------------
-- Execution Context
--------------------------------------------------------------------------------

||| Kinds of work packages.
public export
data PkgKind : Type where
  ||| CPU-bound work packages. This is the default.
  CPU      : PkgKind

  ||| Blocking `IO` actions such as file input/output.
  Blocking : PkgKind

  ||| Work scheduled to run at a specific time.
  Timed    : PkgKind

||| Idris type of work packages based on their kind.
public export
0 PkgType : PkgKind -> Type
PkgType CPU      = PrimIO ()
PkgType Blocking = PrimIO ()
PkgType Timed    = TimerTask

||| Initial work package sent to an execution context.
|||
||| Most work will be run on one of the worker threads of a thread pool,
||| so this provides a way for the worker to inform the work package how
||| to cede itself to later execuption. This allows us to evaluate a single
||| fiber mostly on one thread except even in the face of (auto)-ceding.
public export
record Package where
  constructor Pkg
  cont : Ref ((k : PkgKind) -> PkgType k -> PrimIO ())
  act  : PrimIO ()

||| A context for submitting and running work packages asynchronously.
public export
record ExecutionContext where
  [noHints]
  constructor EC
  spawn : Package -> PrimIO ()
  start : PrimIO ()

--------------------------------------------------------------------------------
-- Synchronous Implementation
--------------------------------------------------------------------------------

record Task where
  constructor T
  kind : PkgKind
  act  : PkgType kind

runTimed : Ref (Queue Task) -> TimerTask -> PrimIO ()
runTimed q t@(TT due cncl run) w =
  let MkIORes False w := readRef cncl w | MkIORes _ w => MkIORes () w
      MkIORes now   w := toPrim (clockTime Monotonic) w
   in case now >= due of
        True  => run w
        False => enq q (T Timed t) w

||| A synchronous execution context running all asynchronous computations
||| on the calling thread.
|||
||| This will block the calling thread after submitting a work package until
||| the package has been completed.
export covering
sync : IO (ExecutionContext)
sync = do
  q  <- primIO (newRef Queue.empty)
  pure $ EC (spawn q) (runQueue q)

  where
    covering
    runQueue : Ref (Queue Task) -> PrimIO ()
    runQueue ref w =
      let MkIORes (Just $ T k a) w := deq ref w | MkIORes _ w => MkIORes () w
       in case k of
            CPU      => let MkIORes _ w := a w in runQueue ref w
            Blocking => let MkIORes _ w := a w in runQueue ref w
            Timed    => let MkIORes _ w := runTimed ref a w in runQueue ref w

    covering
    submit : Ref (Queue Task) -> (k : PkgKind) -> PkgType k -> PrimIO ()
    submit ref k act w =
      let MkIORes _ w := enq ref (T k act) w
       in runQueue ref w

    covering
    spawn : Ref (Queue Task) -> Package -> PrimIO ()
    spawn ref p w =
      let MkIORes _ w := writeRef p.cont (submit ref) w
       in enq ref (T CPU p.act) w
