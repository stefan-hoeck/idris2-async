||| Mutable references exposed in `PrimIO`. This includes the ability
||| to mutate via a CAS-loop to avoid locking with a mutex in certain
||| occasions.
module IO.Async.Internal.Ref

import Data.Queue
import IO.Async.Internal.Concurrent

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

-- Implemented externally
-- e.g., in Scheme, passed around as a box
data Mut : Type where [external]

%foreign "scheme:(lambda (x) (box x))"
         "javascript:lambda:(x) => ({value : x})"
prim__newRef   : AnyPtr -> Mut

%foreign "scheme:(lambda (x) (unbox x))"
         "javascript:lambda:(x) => x.value"
prim__readRef  : Mut -> AnyPtr

%foreign "scheme:(lambda (x v) (set-box! x v))"
         "javascript:lambda:(x,v,t) => {x.value = v}"
prim__writeRef : Mut -> (val : AnyPtr) -> PrimIO ()

%foreign "scheme:(lambda (x v w) (if (box-cas! x v w) 1 0))"
         "javascript:lambda:(x,v,w) => {x.value = w; return 1;}"
prim__casRef : Mut -> (prev,val : AnyPtr) -> Bits8

--------------------------------------------------------------------------------
-- Ref
--------------------------------------------------------------------------------

export
data Ref : (a : Type) -> Type where
  MkRef : Mut -> Ref a

export %noinline
newRef : a -> PrimIO (Ref a)
newRef v = MkIORes (MkRef (prim__newRef $ believe_me v))

export %inline
readRef : Ref a -> PrimIO a
readRef (MkRef m) = MkIORes (believe_me $ prim__readRef m)

export %inline
writeRef : Ref a -> a -> PrimIO ()
writeRef (MkRef m) v = prim__writeRef m (believe_me v)

export %inline
modRef : Ref a -> (a -> a) -> PrimIO ()
modRef r f w = let MkIORes v w := readRef r w in writeRef r (f v) w

||| Thread-safe modification of a mutable reference using a CAS-loop
||| internally
export
modify : Ref a -> (a -> (a,b)) -> PrimIO b
modify (MkRef m) f w = MkIORes (assert_total $ loop) w
  where
    covering loop : b
    loop =
      let cur     := prim__readRef m
          (new,v) := f (believe_me cur)
       in case prim__casRef m cur (believe_me new) of
            1 => v 
            _ => loop

export %inline
update : Ref a -> (a -> a) -> PrimIO ()
update r f = modify r (\v => (f v, ()))

||| Atomically updates the current value in a mutable reference,
||| returning the old value as the result.
export %inline
getAndUpdate : Ref a -> (a -> a) -> PrimIO a
getAndUpdate r f = modify r (\v => (f v, v))

||| Atomically updates the current value in a mutable reference,
||| returning the updated value as the result.
export %inline
updateAndGet : Ref a -> (a -> a) -> PrimIO a
updateAndGet r f = modify r (\v => let w := f v in (w,w))

||| Atomically sets a value if it has not already been set.
||| Returns the value the reference actually holds as a result.
export %inline
put : Ref (Maybe a) -> a -> PrimIO a
put r v =
  modify r $ \case
    Just w  => (Just w, w)
    Nothing => (Just v, v)

export %inline
syncEmpty : Ref (SnocList a) -> PrimIO (SnocList a)
syncEmpty ref = modify ref ([<],)

--------------------------------------------------------------------------------
-- MQueue
--------------------------------------------------------------------------------

export
enq : Ref (Queue a) -> a -> PrimIO ()
enq ref v w =
  let MkIORes x w := readRef ref w
   in writeRef ref (enqueue x v) w

export
deq : Ref (Queue a) -> PrimIO (Maybe a)
deq ref w =
  let MkIORes q w := readRef ref w
   in case dequeue q of
        Just (v,q2) =>
          let MkIORes _ w := writeRef ref q2 w
           in MkIORes (Just v) w
        Nothing => MkIORes Nothing w

export
syncDeq : Ref (Queue a) -> PrimIO (Maybe a)
syncDeq ref =
  modify ref $ \q => case dequeue q of
    Just (v,q2) => (q2, Just v)
    Nothing     => (q, Nothing)
