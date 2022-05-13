module Data.NumIdr.Array.Order

import Data.Vect
import Data.Permutation

%default total


||| An order is an abstract representation of the way in which array
||| elements are stored in memory. Orders are used to calculate strides,
||| which provide a method of converting an array coordinate into a linear
||| memory location.
|||
||| @ rk The rank of the array this order applies to
public export
data Order : (rk : Nat) -> Type where

  ||| C-like order, or contiguous order. This order stores elements in a
  ||| row-major fashion (the last axis is the least significant).
  COrder : Order rk

  ||| Fortran-like order. This order stores elements in a column-major
  ||| fashion (the first axis is the least significant).
  FOrder : Order rk


export
orderOfShape : (0 s : Vect rk Nat) -> Order (length s) -> Order rk
orderOfShape s ord = rewrite sym (lengthCorrect s) in ord



scanr : (el -> res -> res) -> res -> Vect len el -> Vect (S len) res
scanr _ q0 []      = [q0]
scanr f q0 (x::xs) = f x (head qs) :: qs
  where qs : Vect len res
        qs = scanr f q0 xs

||| Calculate an array's strides given its order and shape.
export
calcStrides : Order rk -> Vect rk Nat -> Vect rk Nat
calcStrides _      []        = []
calcStrides COrder v@(_::_)  = scanr (*) 1 $ tail v
calcStrides FOrder v@(_::_)  = scanl (*) 1 $ init v
