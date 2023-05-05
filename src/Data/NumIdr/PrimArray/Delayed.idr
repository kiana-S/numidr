module Data.NumIdr.PrimArray.Delayed

import Data.Vect
import Data.NP
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords

%default total

public export
PrimArrayDelayed : Vect rk Nat -> Type -> Type
PrimArrayDelayed s a = Coords s -> a


export
constant : (s : Vect rk Nat) -> a -> PrimArrayDelayed s a
constant s x _ = x


export
checkRange : (s : Vect rk Nat) -> Vect rk Nat -> Maybe (Coords s)
checkRange [] [] = Just []
checkRange (d :: s) (i :: is) = (::) <$> natToFin i d <*> checkRange s is
