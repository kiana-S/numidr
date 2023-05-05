module Data.NumIdr.Array.Rep

import Data.Vect

%default total


--------------------------------------------------------------------------------
-- Array orders
--------------------------------------------------------------------------------


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


||| Calculate an array's strides given its order and shape.
export
calcStrides : Order -> Vect rk Nat -> Vect rk Nat
calcStrides _      []        = []
calcStrides COrder v@(_::_)  = scanr (*) 1 $ tail v
calcStrides FOrder v@(_::_)  = scanl (*) 1 $ init v


--------------------------------------------------------------------------------
-- Array representations
--------------------------------------------------------------------------------


public export
data Rep : Type where
  Bytes : Order -> Rep
  Boxed : Order -> Rep
  Linked : Rep
  Delayed : Rep

public export
B : Rep
B = Boxed COrder

public export
L : Rep
L = Linked

public export
D : Rep
D = Delayed


public export
data LinearRep : Rep -> Type where
  BytesIsL : LinearRep (Bytes o)
  BoxedIsL : LinearRep (Boxed o)
