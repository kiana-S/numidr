module Data.NumIdr.Array.Order

import Data.Vect
import Data.Permutation

%default total


export
Order : (rk : Nat) -> Type
Order = Permutation

export
COrder : {rk : Nat} -> Order rk
COrder = identity

export
FOrder : {rk : Nat} -> Order rk
FOrder = reversed


scanr : (el -> res -> res) -> res -> Vect len el -> Vect (S len) res
scanr _ q0 []      = [q0]
scanr f q0 (x::xs) = f x (head qs) :: qs
  where qs : Vect len res
        qs = scanr f q0 xs

export
calcStrides : Order rk -> Vect rk Nat -> Vect rk Nat
calcStrides ord v = permuteVect ord $ tail $ scanr (*) 1 v
