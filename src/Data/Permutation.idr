module Data.Permutation

import Data.List
import Data.Vect
import Data.NumIdr.Multiply


export
record Permutation n where
  constructor MkPerm
  swaps : List (Fin n, Fin n)


export
swap : (i,j : Fin n) -> Permutation n
swap x y = MkPerm [(x,y)]

export
appendSwap : (i,j : Fin n) -> Permutation n -> Permutation n
appendSwap i j (MkPerm a) = MkPerm ((i,j)::a)

export
prependSwap : (i,j : Fin n) -> Permutation n -> Permutation n
prependSwap i j (MkPerm a) = MkPerm (a `snoc` (i,j))


mon : Monoid (a -> a)
mon = MkMonoid @{MkSemigroup (.)} id


export
swapElems : (i,j : Fin n) -> Vect n a -> Vect n a
swapElems i j v =
  if i == j then v
  else let x = index i v
           y = index j v
           in replaceAt j x $ replaceAt i y v

export
permuteVect : Permutation n -> Vect n a -> Vect n a
permuteVect p = foldMap @{%search} @{mon} (\(i,j) => swapElems i j) p.swaps


export
swapValues : (i,j : Fin n) -> Nat -> Nat
swapValues i j x = if x == cast i then cast j
                   else if x == cast j then cast i
                   else x

export
permuteValues : Permutation n -> Nat -> Nat
permuteValues p = foldMap @{%search} @{mon} (\(i,j) => swapValues i j) p.swaps

export
Mult (Permutation n) (Permutation n) (Permutation n) where
  MkPerm a *. MkPerm b = MkPerm (a ++ b)

export
MultMonoid (Permutation n) where
  identity = MkPerm []

export
MultGroup (Permutation n) where
  inverse (MkPerm a) = MkPerm (reverse a)
