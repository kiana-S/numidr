module Data.NumIdr.Interfaces

%default total


--------------------------------------------------------------------------------
-- Field
--------------------------------------------------------------------------------


||| An interface synonym for types which form a field, such as `Double`.
public export
Field : Type -> Type
Field a = (Eq a, Neg a, Fractional a)


||| An interface for number types which allow for LUP decomposition to be performed.
|||
||| The function `abslt` is required for the internal decomposition algorithm.
||| An instance of this interface must satisfy:
||| * The relation `abslt` is a preorder.
||| * `0` is a minimum of `abslt`.
public export
interface (Eq a, Neg a, Fractional a) => FieldCmp a where
  constructor MkFieldCmp
  ||| Compare the absolute values of two inputs.
  abslt : a -> a -> Bool


export
(Ord a, Abs a, Neg a, Fractional a) => FieldCmp a where
  abslt x y = abs x < abs y


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
  constructor MkMult
  ||| A generalized multiplication/application operator for matrices and
  ||| vector transformations.
  (*.) : a -> b -> c

||| A synonym for `Mult a a a`, or homogenous multiplication.
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
  constructor MkMultMonoid
  ||| Construct an identity matrix or transformation.
  |||
  ||| NOTE: Creating an identity element for an `n`-dimensional transformation
  ||| usually requires `n` to be available at runtime.
  identity : a

||| An interface for groups using the `*.` operator.
|||
||| An instance of this interface must satisfy:
||| * `x *. inverse x == identity`
||| * `inverse x *. x == identity`
public export
interface MultMonoid a => MultGroup a where
  constructor MkMultGroup
  ||| Calculate the inverse of the matrix or transformation.
  ||| WARNING: This function will not check if an inverse exists for the given
  ||| input, and will happily return results containing NaN values. To avoid
  ||| this, use `tryInverse` instead.
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
