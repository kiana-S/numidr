module Data.NumIdr.Scalar

import Data.Vect
import Data.NumIdr.Multiply
import Data.NumIdr.PrimArray
import public Data.NumIdr.Array

%default total

||| Scalars are `Array []`, the unique 0-rank array type. They hold a single value.
||| Scalars are not particularly useful as container types, but they are
||| included here anyways.
public export
Scalar : Type -> Type
Scalar = Array []


||| Convert a value to a scalar.
export
scalar : a -> Scalar a
scalar x = fromVect _ [x]

||| Unwrap the single value from a scalar.
export
unwrap : Scalar a -> a
unwrap = index 0 . getPrim


export
Num a => Mult (Scalar a) (Scalar a) (Scalar a) where
  (*.) = (*)
