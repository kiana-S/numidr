module Data.NumIdr.Array

import Data.Vect
import Data.NumIdr.PrimArray

%default total


export
data Array : Vect rank Nat -> Type -> Type where
  MkArray : PrimArray a -> Array dim a



export
size : Array dim a -> Nat
size (MkArray arr) = length arr

export
fromVect : {0 dim : Vect rank Nat} -> Vect (product dim) a -> Array dim a
fromVect = MkArray . fromList . toList

export
reshape : {0 dim : Vect rank Nat} -> (0 dim' : Vect rank' Nat) ->
           Array dim a -> product dim = product dim' =>
           Array dim' a
reshape _ (MkArray arr) = MkArray arr

Vects : Vect rank Nat -> Type -> Type
Vects [] a = a
Vects (d :: dim) a = Vect d (Vects dim a)



export
constant : a -> (dim : Vect rank Nat) -> Array dim a
constant x dim = MkArray $ create (product dim) (const x)

export
zeros : Num a => (dim : Vect rank Nat) -> Array dim a
zeros = constant 0
