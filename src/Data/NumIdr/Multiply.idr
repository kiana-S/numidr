module Data.NumIdr.Multiply

%default total


infixr 9 *.
infixr 10 ^

||| A generalized multiplication/transformation operator. This interface is
||| necessary since the standard multiplication operator is homogenous.
public export
interface Mult a b c | a,b where
  (*.) : a -> b -> c

public export
interface (Mult a a a) => MultNeutral a where
  neutral : a


public export
[MultSemigroup] Mult a a a => Semigroup a where
  (<+>) = (*.)

public export
[MultMonoid] MultNeutral a => Monoid a using MultSemigroup where
  neutral = Multiply.neutral


public export
power : MultNeutral a => Nat -> a -> a
power 0 _ = neutral
power 1 x = x
power (S n@(S _)) x = x *. power n x

public export
(^) : MultNeutral a => a -> Nat -> a
(^) = flip power
