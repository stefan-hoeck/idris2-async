module IO.Async.MCancel

import public Control.Monad.MErr
import public IO.Async.Outcome

%default total

public export
0 Poll : (f : List Type -> Type -> Type) -> Type
Poll f = forall es,a . f es a -> f es a

public export
interface MErr f => MCancel f where
  ||| Requests self-cancelation of the current fiber (computational thread).
  canceled : f es ()

  ||| Masks cancelation on the current fiber. The argument to `body` of type `Poll f` is a
  ||| natural transformation `f ~> f` that enables polling. Polling causes a fiber to unmask
  ||| within a masked region so that cancelation can be observed again.
  ||| 
  ||| In the following example, cancelation can be observed only within `fb` and nowhere else:
  ||| 
  ||| ```
  |||   uncancelable $ \poll => fa >> poll(fb) >> fc
  ||| ```
  ||| 
  ||| If a fiber is canceled while it is masked, the cancelation is suppressed for as long as the
  ||| fiber remains masked. Whenever the fiber is completely unmasked again, the cancelation will
  ||| be respected.
  ||| 
  ||| Masks can also be stacked or nested within each other. If multiple masks are active, all
  ||| masks must be undone so that cancelation can be observed. In order to completely unmask
  ||| within a multi-masked region the poll corresponding to each mask must be applied to the
  ||| effect, outermost-first.
  ||| 
  ||| ```
  |||   uncancelable $ \p1 =>
  |||     uncancelable $ \p2 =>
  |||       fa >> p2(p1(fb)) >> fc
  ||| ```
  ||| 
  ||| The following operations are no-ops:
  ||| 
  |||   1. Polling in the wrong order
  |||   2. Subsequent polls when applying the same poll more than once: `poll(poll(fa))` is
  |||      equivalent to `poll(fa)`
  |||   3. Applying a poll bound to one fiber within another fiber
  uncancelable : (body: Poll f -> f es a) -> f es a

  ||| Registers a finalizer that is invoked if cancelation is observed during the evaluation of
  ||| `fa`. If the evaluation of `fa` completes without encountering a cancelation, the finalizer
  ||| is unregistered before proceeding.
  ||| 
  ||| Note that if `fa` is uncancelable (e.g. created via `uncancelable`) then `fin` won't be
  ||| fired.
  ||| 
  ||| ```
  |||   onCancel (uncancelable(_ => canceled)) fin <-> F.unit
  ||| ```
  ||| 
  ||| During finalization, all actively registered finalizers are run exactly once. The order by
  ||| which finalizers are run is dictated by nesting: innermost finalizers are run before
  ||| outermost finalizers. For example, in the following program, the finalizer `f1` is run
  ||| before the finalizer `f2`:
  ||| 
  ||| ```
  |||   onCancel (onCancel canceled f1) f2
  ||| ```
  ||| 
  ||| In accordance with the type signatur, finalizers must not throw observable
  ||| errors
  onCancel : f es a -> f [] () -> f es a

parameters {0    f  : List Type -> Type -> Type}
           {auto mc : MCancel f}

  ||| Specifies an effect that is always invoked after evaluation of `fa` completes, but depends
  ||| on the outcome.
  ||| 
  ||| See also `bracketCase` for a more powerful variant
  export
  guaranteeCase : f es a -> (Outcome es a -> f [] ()) -> f es a
  guaranteeCase act fin =
    uncancelable $ \poll => do
      v <- onError (onCancel (poll act) (fin Canceled)) (fin . Error)
      weakenErrors (fin $ Succeeded v)
      pure v

  ||| Specifies an effect that is always invoked after evaluation of `fa` completes, regardless
  ||| of the outcome.
  ||| 
  ||| See `guaranteeCase` for a more powerful variant
  export %inline
  guarantee : f es a -> f [] () -> f es a
  guarantee act = guaranteeCase act . const

  ||| A pattern for safely interacting with effectful lifecycles.
  ||| 
  ||| If `acquire` completes successfully, `use` is called. If `use` succeeds, fails, or is
  ||| canceled, `release` is guaranteed to be called exactly once.
  ||| 
  ||| If `use` succeeds the returned value `B` is returned. If `use` returns an exception, the
  ||| exception is returned.
  ||| 
  ||| `acquire` is uncancelable by default, but can be unmasked. `release` is uncancelable. `use`
  ||| is cancelable by default, but can be masked.
  export
  bracketFull :
       (acquire : Poll f -> f es a)
    -> (use     : a -> f es b)
    -> (release : a -> Outcome es b -> f [] ())
    -> f es b
  bracketFull acquire use release =
    uncancelable $ \poll => do
      v <- acquire poll
      guaranteeCase (poll $ use v) (release v)
  
  ||| A pattern for safely interacting with effectful lifecycles.
  ||| 
  ||| If `acquire` completes successfully, `use` is called. If `use` succeeds, fails, or is
  ||| canceled, `release` is guaranteed to be called exactly once.
  ||| 
  ||| `acquire` is uncancelable. `release` is uncancelable. `use` is cancelable by default, but
  ||| can be masked.
  export %inline
  bracketCase :
       (acquire : f es a)
    -> (use     : a -> f es b)
    -> (release : a -> Outcome es b -> f [] ())
    -> f es b
  bracketCase = bracketFull . const
  
  ||| A pattern for safely interacting with effectful lifecycles.
  ||| 
  ||| If `acquire` completes successfully, `use` is called. If `use` succeeds, fails, or is
  ||| canceled, `release` is guaranteed to be called exactly once.
  ||| 
  ||| `acquire` is uncancelable. `release` is uncancelable. `use` is cancelable by default, but
  ||| can be masked.
  export %inline
  bracket :
       (acquire : f es a)
    -> (use     : a -> f es b)
    -> (release : a -> f [] ())
    -> f es b
  bracket acquire use release = bracketCase acquire use (const . release)
