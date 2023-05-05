module Data.NumIdr.PrimArray.Linked

import Data.Vect
import Data.NP
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords

%default total


export
constant : (s : Vect rk Nat) -> a -> Vects s a
constant [] x = x
constant (d :: s) xs = replicate d (constant s xs)

export
index : Coords s -> Vects s a -> a
index [] x = x
index (c :: cs) xs = index cs (index c xs)


export
fromFunction : {s : _} -> (Coords s -> a) -> Vects s a
fromFunction {s = []} f = f []
fromFunction {s = d :: s} f = tabulate (\i => fromFunction (f . (i::)))

export
fromFunctionNB : {s : _} -> (Vect rk Nat -> a) -> Vects {rk} s a
fromFunctionNB {s = []} f = f []
fromFunctionNB {s = d :: s} f = tabulate' {n=d} (\i => fromFunctionNB (f . (i::)))
  where
    tabulate' : forall a. {n : _} -> (Nat -> a) -> Vect n a
    tabulate' {n=Z} f = []
    tabulate' {n=S _} f = f Z :: tabulate' (f . S)
