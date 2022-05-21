module Data.NumIdr.Scalar

import Data.Vect
import Data.NumIdr.PrimArray
import public Data.NumIdr.Array

%default total

||| Scalars are `Array []`, the unique 0-rank array type. They hold a single value.
||| Scalars are not particularly useful as container types, but they are
||| included here anyways.
public export
Scalar : Type -> Type
Scalar = Array []


export
scalar : a -> Scalar a
scalar x = fromVect _ [x]

export
unwrap : Scalar a -> a
unwrap = index 0 . getPrim
