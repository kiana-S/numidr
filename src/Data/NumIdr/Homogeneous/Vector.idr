module Data.NumIdr.Homogeneous.Vector

import Data.Vect
import Data.NumIdr.Multiply
import public Data.NumIdr.Vector

%default total


public export
HVector : Nat -> Type -> Type
HVector n = Vector (S n)




export
fromVector : Num a => Vector n a -> HVector n a
fromVector v = rewrite plusCommutative 1 n in v ++ vector [1]

export
fromVectorL : Num a => Vector n a -> HVector n a
fromVectorL v = rewrite plusCommutative 1 n in v ++ vector [0]

export
toVector : HVector n a -> Vector n a
toVector = vector . init . toVect
-- TODO: Find an implementation for `toVector` that doesn't suck

