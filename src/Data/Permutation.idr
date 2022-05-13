module Data.Permutation

import Data.Vect

%default total


||| A permutation of `n` elements represented as a vector of indices.
||| For example, `[1,2,0]` is a permutation that maps element `0` to
||| element `1`, element `1` to element `2`, and element `2` to element `0`.
public export
Permutation : (n : Nat) -> Type
Permutation n = Vect n (Fin n)


||| The identity permutation.
public export
identity : {n : _} -> Permutation n
identity {n=Z} = []
identity {n=S n} = FZ :: map FS identity

||| The permutation that reverses the order of elements.
public export
reversed : {n : _} -> Permutation n
reversed {n=Z} = []
reversed {n=S n} = last :: map weaken reversed


||| Apply a permutation to a vector.
public export
permuteVect : Permutation n -> Vect n a -> Vect n a
permuteVect p v = map (\i => index i v) p
