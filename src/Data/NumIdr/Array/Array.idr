module Data.NumIdr.Array.Array

import Data.Vect
import Data.NumIdr.PrimArray
import Data.NumIdr.Array.Order
import Data.NumIdr.Array.Coords

%default total


export
data Array : Vect rk Nat -> Type -> Type where
  MkArray : (sts : Vect rk Nat) -> (s : Vect rk Nat) -> PrimArray a -> Array s a


export
getPrim : Array s a -> PrimArray a
getPrim (MkArray _  _ arr) = arr

export
getStrides : Array {rk} s a -> Vect rk Nat
getStrides (MkArray sts _ _) = sts

export
size : Array s a -> Nat
size = length . getPrim

export
shape : Array {rk} s a -> Vect rk Nat
shape (MkArray _ s _) = s

export
rank : Array s a -> Nat
rank = length . shape



export
fromVect' : (s : Vect rk Nat) -> Order rk -> Vect (product s) a -> Array s a
fromVect' s ord v = MkArray (calcStrides ord s) s (fromList $ toList v)

export
fromVect : (s : Vect rk Nat) -> Vect (product s) a -> Array s a
fromVect s = fromVect' s (orderOfShape s COrder)



export
array' : (s : Vect rk Nat) -> Order rk -> Vects s a -> Array s a
array' s ord v = MkArray sts s (unsafeFromIns (product s) ins)
  where
    sts : Vect rk Nat
    sts = calcStrides ord s

    ins : List (Nat, a)
    ins = collapse $ mapWithIndex (\i,x => (sum $ zipWith (*) i sts, x)) v


export
reshape' : (s' : Vect rk' Nat) -> Order rk' -> Array {rk} s a ->
             product s = product s' => Array s' a
reshape' s' ord' arr = MkArray (calcStrides ord' s') s' (getPrim arr)

export
reshape : (s' : Vect rk' Nat) -> Array {rk} s a ->
            product s = product s' => Array s' a
reshape s' = reshape' s' (orderOfShape s' COrder)


export
index : Coords s -> Array s a -> a
index is arr = index (computeLoc (getStrides arr) is) (getPrim arr)


export
test : Array [2,2,3] Int
test = array' _ FOrder [[[1,2,3],[4,5,6]],[[7,8,9],[10,11,12]]]

export
main : IO ()
main = do
        printLn $ index [0,1,0] test
        printLn $ index [1,1,2] test
