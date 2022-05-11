module Data.NumIdr.Array

import Data.Vect
import Data.Reify
import Data.NumIdr.PrimArray

%default total


export
record Array {0 rk : Nat} (s : Vect rk Nat) a where
  constructor MkArray
  shape : Reify s
  contents : PrimArray a

mkArray : {s : _} -> PrimArray a -> Array s a
mkArray arr = MkArray (MkReify _) arr


export
size : Array s a -> Nat
size arr = length arr.contents

export
shape : {0 s : Vect rk Nat} -> Array s a -> Vect rk Nat
shape arr = getReify arr.shape

export
rank : Array s a -> Nat
rank arr = length $ shape arr

export
fromVect : {s : Vect rk Nat} -> Vect (product s) a -> Array s a
fromVect = mkArray . fromList . toList

public export
Vects : Vect rk Nat -> Type -> Type
Vects [] a = a
Vects (d :: s) a = Vect d (Vects s a)

export
fromVects : {s : _} -> Vects s a -> Array s a
fromVects = mkArray . fromList . collapse
  where
    collapse : {s : Vect rk Nat} -> Vects s a -> List a
    collapse {s=[]} x = [x]
    collapse {s=_::_} v = concat $ map collapse v

export
reshape : {0 s : Vect rk Nat} -> (s' : Vect rk' Nat) ->
           Array s a -> product s = product s' =>
           Array s' a
reshape _ arr = mkArray arr.contents



export
constant : a -> (s : Vect rk Nat) -> Array s a
constant x s = mkArray $ create (product s) (const x)

export
zeros : Num a => (s : Vect rk Nat) -> Array s a
zeros = constant 0
