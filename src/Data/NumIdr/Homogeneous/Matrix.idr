module Data.NumIdr.Homogeneous.Matrix

import Data.Vect
import Data.NumIdr.Multiply
import public Data.NumIdr.Matrix

%default total


public export
HMatrix : Nat -> Nat -> Type -> Type
HMatrix m n = Matrix (S m) (S n)




export
fromMatrix : Num a => Matrix m n a -> HMatrix m n a
fromMatrix mat = withDims mat $ \m,n,mat => ?h2 -- rewrite plusCommutative 1 m in ?h -- (mat `vconcat` repeat [1,n] 0) `hconcat` repeat [m,1] 0

export
toMatrix : HMatrix m n a -> Matrix m n a
toMatrix = ?h
