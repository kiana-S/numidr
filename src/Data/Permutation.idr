module Data.Permutation

import Data.List
import Data.Vect
import Data.NumIdr.Interfaces

%default total

||| A permutation in `n` elements.
|||
||| Permutations are internally stored as a list of elements to swap in
||| right-to-left order. This allows for easy composition and inversion of
||| permutation values.
export
record Permutation n where
  constructor MkPerm
  swaps : List (Fin n, Fin n)


||| Construct a permutation that swaps two elements.
export
swap : (i,j : Fin n) -> Permutation n
swap x y = MkPerm [(x,y)]

||| Construct a permutation that makes the listed swaps in right-to-left order.
export
swaps : List (Fin n, Fin n) -> Permutation n
swaps = MkPerm

||| Add a swap to the end of a permutation.
|||
||| `appendSwap sw p = swap sw *. p`
export
appendSwap : (i,j : Fin n) -> Permutation n -> Permutation n
appendSwap i j (MkPerm a) = MkPerm ((i,j)::a)

||| Add a swap to the beginning of a permutation.
|||
||| `prependSwap sw p = p *. swap sw`
export
prependSwap : (i,j : Fin n) -> Permutation n -> Permutation n
prependSwap i j (MkPerm a) = MkPerm (a `snoc` (i,j))


mon : Monoid (a -> a)
mon = MkMonoid @{MkSemigroup (.)} id


||| Swap two elements of a `Vect`.
export
swapElems : (i,j : Fin n) -> Vect n a -> Vect n a
swapElems i j v =
  if i == j then v
  else let x = index i v
           y = index j v
           in replaceAt j x $ replaceAt i y v

||| Permute the elements of a `Vect`.
export
permuteVect : Permutation n -> Vect n a -> Vect n a
permuteVect p = foldMap @{%search} @{mon} (uncurry swapElems) p.swaps


||| Construct a function that swaps two values.
export
swapValues : (i,j : Fin n) -> Nat -> Nat
swapValues i j x = if x == cast i then cast j
                   else if x == cast j then cast i
                   else x

||| Construct a function that permutes values.
export
permuteValues : Permutation n -> Nat -> Nat
permuteValues p = foldMap @{%search} @{mon} (uncurry swapValues) p.swaps



export
Show (Permutation n) where
  showPrec p (MkPerm a) = showCon p "swaps" $ showArg a

export
Mult (Permutation n) (Permutation n) (Permutation n) where
  MkPerm a *. MkPerm b = MkPerm (a ++ b)

export
MultMonoid (Permutation n) where
  identity = MkPerm []

export
MultGroup (Permutation n) where
  inverse (MkPerm a) = MkPerm (reverse a)
