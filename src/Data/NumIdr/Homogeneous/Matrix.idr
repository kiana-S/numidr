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
fromMatrix mat with (viewShape mat)
  _ | Shape [m,n] = ?h2

export
toMatrix : HMatrix m n a -> Matrix m n a
toMatrix = ?h
