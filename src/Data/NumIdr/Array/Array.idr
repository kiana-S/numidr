module Data.NumIdr.Array.Array

import Data.Vect
import Data.NumIdr.PrimArray
import Data.NumIdr.Array.Order

%default total


export
data Array : Vect rk Nat -> Type -> Type where
  MkArray : (ord : Order rk) -> (sts : Vect rk Nat) ->
              (s : Vect rk Nat) -> PrimArray a -> Array s a


export
getPrim : Array s a -> PrimArray a
getPrim (MkArray _ _ _ arr) = arr

export
getOrder : Array {rk} s a -> Order rk
getOrder (MkArray ord _ _ _) = ord

export
getStrides : Array {rk} s a -> Vect rk Nat
getStrides (MkArray _ sts _ _) = sts

export
size : Array s a -> Nat
size = length . getPrim

export
shape : Array {rk} s a -> Vect rk Nat
shape (MkArray _ _ s _) = s

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


export
reshape' : (s' : Vect rk' Nat) -> Order rk -> Array {rk} s a ->
             product s = product s' => Array rk' s' a
reshape' s' ord arr = MkArray 
