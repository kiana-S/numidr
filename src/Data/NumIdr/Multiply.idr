module Data.NumIdr.Multiply

%default total


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

||| An interface for monoids using the `*.` operator.
|||
||| An instance of this interface must satisfy:
||| * `x *. neutral == x`
||| * `neutral *. x == x`
public export
interface Mult a a a => MultNeutral a where
  neutral : a


||| Multiplication forms a semigroup
public export
[MultSemigroup] Mult a a a => Semigroup a where
  (<+>) = (*.)

||| Multiplication with a neutral element forms a monoid
public export
[MultMonoid] MultNeutral a => Monoid a using MultSemigroup where
  neutral = Multiply.neutral


||| Raise a multiplicative value (e.g. a matrix or a transformation) to a natural
||| number power.
public export
power : MultNeutral a => Nat -> a -> a
power 0 _ = neutral
power 1 x = x
power (S n@(S _)) x = x *. power n x

||| Raise a multiplicative value (e.g. a matrix or a transformation) to a natural
||| number power.
|||
||| This is the operator form of `power`.
public export
(^) : MultNeutral a => a -> Nat -> a
(^) = flip power
