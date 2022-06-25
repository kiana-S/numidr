module Data.NumIdr.Array.Order

import Data.Vect

%default total


||| An order is an abstract representation of the way in which array
||| elements are stored in memory. Orders are used to calculate strides,
||| which provide a method of converting an array coordinate into a linear
||| memory location.
public export
data Order : Type where

  ||| C-like order, or contiguous order. This order stores elements in a
  ||| row-major fashion (the last axis is the least significant).
  COrder : Order

  ||| Fortran-like order. This order stores elements in a column-major
  ||| fashion (the first axis is the least significant).
  FOrder : Order


public export
Eq Order where
  COrder == COrder = True
  FOrder == FOrder = True
  COrder == FOrder = False
  FOrder == COrder = False


scanr : (el -> res -> res) -> res -> Vect len el -> Vect (S len) res
scanr _ q0 []      = [q0]
scanr f q0 (x::xs) = f x (head qs) :: qs
  where qs : Vect len res
        qs = scanr f q0 xs

||| Calculate an array's strides given its order and shape.
export
calcStrides : Order -> Vect rk Nat -> Vect rk Nat
calcStrides _      []        = []
calcStrides COrder v@(_::_)  = scanr (*) 1 $ tail v
calcStrides FOrder v@(_::_)  = scanl (*) 1 $ init v
