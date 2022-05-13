module Data.NumIdr.Array.Order

import Data.Vect
import Data.Permutation

%default total


public export
data Order : (rk : Nat) -> Type where
  COrder : Order rk
  FOrder : Order rk


export
orderOfShape : (0 s : Vect rk Nat) -> Order (length s) -> Order rk
orderOfShape s ord = rewrite sym (lengthCorrect s) in ord



scanr : (el -> res -> res) -> res -> Vect len el -> Vect (S len) res
scanr _ q0 []      = [q0]
scanr f q0 (x::xs) = f x (head qs) :: qs
  where qs : Vect len res
        qs = scanr f q0 xs

export
calcStrides : Order rk -> Vect rk Nat -> Vect rk Nat
calcStrides COrder v = tail $ scanr (*) 1 v
calcStrides FOrder v = init $ scanl (*) 1 v
