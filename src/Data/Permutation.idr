module Data.Permutation

import Data.Vect

%default total


public export
Permutation : Nat -> Type
Permutation n = Vect n (Fin n)


public export
identity : {n : _} -> Permutation n
identity {n=Z} = []
identity {n=S n} = FZ :: map FS identity

public export
reversed : {n : _} -> Permutation n
reversed {n=Z} = []
reversed {n=S n} = last :: map weaken reversed


public export
permuteVect : Permutation n -> Vect n a -> Vect n a
permuteVect p v = map (\i => index i v) p
