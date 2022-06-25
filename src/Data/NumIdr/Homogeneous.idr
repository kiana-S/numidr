module Data.NumIdr.Homogeneous

import Data.Vect
import Data.NumIdr.Multiply
import Data.NumIdr.Vector
import Data.NumIdr.Matrix

%default total



||| A homogeneous matrix type.
|||
||| Homogeneous matrices are matrices that encode an affine transformation, as
||| opposed to the more restriced linear transformations of normal matrices.
||| Their multiplication is identical to regular matrix multiplication, but the
||| extra dimension in each axis allows the homogeneous matrix to store a
||| translation vector that is applied during multiplication.
|||
||| ```hmatrix mat tr *. v == mat *. v + tr```
public export
HMatrix : Nat -> Nat -> Type -> Type
HMatrix m n = Matrix (S m) (S n)

||| A synonym for a square homogeneous matrix.
public export
HMatrix' : Nat -> Type -> Type
HMatrix' n = HMatrix n n

||| An `n`-dimensional homogeneous vector type.
|||
||| Homogeneous vectors are vectors intended to be multiplied with homogeneous
||| matrices (see `HMatrix`). They have an extra dimension compared to regular
||| vectors.
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




export
toHomogeneous : Num a => Matrix m n a -> HMatrix m n a
toHomogeneous mat with (viewShape mat)
  _ | Shape [m,n] = indexSet [last, last] 1 $ resize [S m, S n] 0 mat



export
toMatrix : HMatrix m n a -> Matrix m n a
toMatrix mat with (viewShape mat)
  _ | Shape [S m, S n] = resizeLTE [m,n] mat
                          {ok = [lteSuccRight reflexive,lteSuccRight reflexive]}
