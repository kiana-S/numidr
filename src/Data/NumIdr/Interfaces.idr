module Data.NumIdr.Interfaces

%default total


--------------------------------------------------------------------------------
-- Field
--------------------------------------------------------------------------------


public export
Field : Type -> Type
Field a = (Eq a, Neg a, Fractional a)


public export
interface (Eq a, Neg a, Fractional a) => FieldCmp a where
  abscmp : a -> a -> Ordering


export
(Ord a, Abs a, Neg a, Fractional a) => FieldCmp a where
  abscmp x y = compare (abs x) (abs y)


--------------------------------------------------------------------------------
-- Multiplication
--------------------------------------------------------------------------------

infixr 9 *.
infixr 10 ^

||| A generalized multiplication/application operator. This interface is
||| necessary since the standard multiplication operator is homogenous.
|||
||| All instances of this interface must collectively satisfy these axioms:
||| * If `(x *. y) *. z` is defined, then `x *. (y *. z)` is defined and equal.
||| * If `x *. (y *. z)` is defined, then `(x *. y) *. z` is defined and equal.
public export
interface Mult a b c | a,b where
  (*.) : a -> b -> c

public export
Mult' : Type -> Type
Mult' a = Mult a a a


||| An interface for monoids using the `*.` operator.
|||
||| An instance of this interface must satisfy:
||| * `x *. identity == x`
||| * `identity *. x == x`
public export
interface Mult' a => MultMonoid a where
  identity : a

||| An interface for groups using the `*.` operator.
|||
||| An instance of this interface must satisfy:
||| * `x *. inverse x == identity`
||| * `inverse x *. x == identity`
public export
interface MultMonoid a => MultGroup a where
  inverse : a -> a


namespace Semigroup
  ||| Multiplication forms a semigroup
  public export
  [Mult] Mult' a => Semigroup a where
    (<+>) = (*.)

namespace Monoid
  ||| Multiplication with an identity element forms a monoid
  public export
  [Mult] MultMonoid a => Monoid a using Semigroup.Mult where
    neutral = identity


||| Raise a multiplicative value (e.g. a matrix or a transformation) to a natural
||| number power.
public export
power : MultMonoid a => Nat -> a -> a
power 0 _ = identity
power 1 x = x
power (S n@(S _)) x = x *. power n x

||| Raise a multiplicative value (e.g. a matrix or a transformation) to a natural
||| number power.
|||
||| This is the operator form of `power`.
public export %inline
(^) : MultMonoid a => a -> Nat -> a
a ^ n = power n a
