module IO.Async.Outcome

import public Data.List.Quantifiers.Extra

%default total

||| Alias for `Either (HSum es) a`: A computation that either
||| succeeds with a result of type `a` or fails with an error
||| of one of the types given in list `es`.
|||
||| Note: If `es` is the empty list, the computation cannot fail,
||| because `HSum []` is uninhabited.
public export
0 Result : List Type -> Type -> Type
Result es a = Either (HSum es) a

public export
data Outcome : List Type -> Type -> Type where
  Succeeded : (res : a) -> Outcome es a
  Error     : (err : HSum es) -> Outcome es a
  Canceled  : Outcome es a

export
toOutcome : Result es a -> Outcome es a
toOutcome (Right v)   = Succeeded v
toOutcome (Left errs) = Error errs

export
Functor (Outcome es) where
  map f (Succeeded v) = Succeeded (f v)
  map _ (Error v)     = Error v
  map _ Canceled      = Canceled

export
Foldable (Outcome es) where
  foldr f x (Succeeded v) = f v x
  foldr f x _             = x

  foldl f x (Succeeded v) = f x v
  foldl f x _             = x

  foldMap f (Succeeded v) = f v
  foldMap f _             = neutral

  toList (Succeeded v) = [v]
  toList _             = []

  null (Succeeded v) = False
  null _             = True

export
Traversable (Outcome es) where
  traverse f (Succeeded v) = Succeeded <$> f v
  traverse _ (Error v)     = pure $ Error v
  traverse _ Canceled      = pure Canceled
