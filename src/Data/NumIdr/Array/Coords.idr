module Data.NumIdr.Array.Coords

import Data.Vect

%default total


public export
data Coords : (s : Vect rk Nat) -> Type where
  Nil  : Coords Nil
  (::) : Fin dim -> Coords s -> Coords (dim :: s)

export
toNats : Coords {rk} s -> Vect rk Nat
toNats [] = []
toNats (i :: is) = finToNat i :: toNats is



public export
Vects : Vect rk Nat -> Type -> Type
Vects []     a = a
Vects (d::s) a = Vect d (Vects s a)

export
collapse : {s : _} -> Vects s a -> List a
collapse {s=[]} = (::[])
collapse {s=_::_} = concat . map collapse


export
mapWithIndex : {s : Vect rk Nat} -> (Vect rk Nat -> a -> b) -> Vects {rk} s a -> Vects s b
mapWithIndex {s=[]}   f x = f [] x
mapWithIndex {s=_::_} f v = mapWithIndex' (\i => mapWithIndex (\is => f (i::is))) v
  where
    mapWithIndex' : {0 a,b : Type} -> (Nat -> a -> b) -> Vect n a -> Vect n b
    mapWithIndex' f [] = []
    mapWithIndex' f (x::xs) = f Z x :: mapWithIndex' (f . S) xs


export
index : Coords s -> Vects s a -> a
index []      x = x
index (i::is) v = index is $ index i v


export
computeLoc : Vect rk Nat -> Coords {rk} s -> Nat
computeLoc sts is = sum $ zipWith (*) sts (toNats is)
