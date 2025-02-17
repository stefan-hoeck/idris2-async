module IO.Async.Outcome

import Derive.Prelude
import public Control.Monad.MErr
import public Data.List.Quantifiers.Extra

%default total
%language ElabReflection

public export
data Outcome : List Type -> Type -> Type where
  Succeeded : (res : a) -> Outcome es a
  Error     : (err : HSum es) -> Outcome es a
  Canceled  : Outcome es a

export
All Eq es => Eq a => Eq (Outcome es a) where
  Succeeded x == Succeeded y = x == y
  Error x     == Error y     = x == y
  Canceled    == Canceled    = True
  _           == _           = False

export
All Show es => Show a => Show (Outcome es a) where
  showPrec p (Succeeded x) = showCon p "Succeeded" (showArg x)
  showPrec p (Error x)     = showCon p "Error" (showArg x)
  showPrec p Canceled      = "Canceled"

export
toOutcome : Result es a -> Outcome es a
toOutcome (Right v)   = Succeeded v
toOutcome (Left errs) = Error errs

export
fromOutcome : Outcome es a -> Result es (Maybe a)
fromOutcome (Succeeded v) = Right (Just v)
fromOutcome Canceled      = Right Nothing
fromOutcome (Error es)    = Left es

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

export
Applicative (Outcome es) where
  pure = Succeeded
  Succeeded f <*> Succeeded v = Succeeded (f v)
  Error err   <*> _           = Error err
  Canceled    <*> _           =  Canceled
  _           <*> Error err   = Error err
  _           <*> Canceled    = Canceled

export
Monad (Outcome es) where
  Succeeded v >>= f = f v
  Error x     >>= _ = Error x
  Canceled    >>= _ = Canceled
