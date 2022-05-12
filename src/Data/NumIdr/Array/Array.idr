module Data.NumIdr.Array.Array

import Data.Vect
import Data.Reify
import Data.NumIdr.PrimArray
import Data.NumIdr.Array.Order

%default total


export
record Array {0 rk : Nat} (s : Vect rk Nat) a where
  constructor MkArray
  shape : Reify s
  strides : Vect rk Nat
  contents : PrimArray a


export
getPrim : Array s a -> PrimArray a
getPrim = contents

export
getStrides : Array {rk} s a -> Vect rk Nat
getStrides = strides

export
size : Array s a -> Nat
size arr = length arr.contents

export
shape : Array {rk} s a -> Vect rk Nat
shape arr = getReify arr.shape

export
rank : Array s a -> Nat
rank arr = length $ shape arr



export
fromVect' : (s : Vect rk Nat) -> Order rk -> Vect (product s) a -> Array s a
fromVect' s ord v = MkArray (MkReify s) (calcStrides ord s) (fromList $ toList v)

export
fromVect : (s : Vect rk Nat) -> Vect (product s) a -> Array s a
fromVect s = fromVect' s $ rewrite sym (lengthCorrect s) in COrder {rk = length s}

public export
Vects : Vect rk Nat -> Type -> Type
Vects []     a = a
Vects (d::s) a = Vect d (Vects s a)
