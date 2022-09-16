module Data.NumIdr.Homogeneous

import Data.Vect
import Data.NumIdr.Interfaces
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


--------------------------------------------------------------------------------
-- Conversion functions
--------------------------------------------------------------------------------


export
vectorToH : Num a => Vector n a -> HVector n a
vectorToH v = rewrite plusCommutative 1 n in v ++ vector [1]

export
vectorToHLinear : Num a => Vector n a -> HVector n a
vectorToHLinear v = rewrite plusCommutative 1 n in v ++ vector [0]

export
hvector : Num a => Vect n a -> HVector n a
hvector v = rewrite plusCommutative 1 n in vector (v ++ [1])

export
hvectorLinear : Num a => Vect n a -> HVector n a
hvectorLinear v = rewrite plusCommutative 1 n in vector (v ++ [0])


export
fromHomogeneous : HVector n a -> Vector n a
fromHomogeneous = vector . init . toVect
-- TODO: Find an implementation for `fromHomogeneous` that doesn't suck


export
hmatrix : Num a => Matrix m n a -> Vector m a -> HMatrix m n a
hmatrix {m,n} mat tr with (viewShape mat)
  _ | Shape [m,n] = indexSet [last,last] 1 $
                    resize [S m, S n] 0 $
                    mat `hconcat` reshape
                      {ok = sym $ multOneRightNeutral _} [m,1] tr

export
matrixToH : Num a => Matrix m n a -> HMatrix m n a
matrixToH {m,n} mat with (viewShape mat)
  _ | Shape [m,n] = indexSet [last,last] 1 $ resize [S m, S n] 0 mat



export
getMatrix : HMatrix m n a -> Matrix m n a
getMatrix {m,n} mat with (viewShape mat)
  _ | Shape [S m, S n] = resizeLTE [m,n] mat
                          {ok = [lteSuccRight reflexive,lteSuccRight reflexive]}

export
getTranslationVector : HMatrix m n a -> Vector m a
getTranslationVector {m,n} mat with (viewShape mat)
  _ | Shape [S m, S n] = resizeLTE [m] {ok = [lteSuccRight reflexive]} $
                          getColumn last mat


--------------------------------------------------------------------------------
-- Constructors of homogeneous matrices
--------------------------------------------------------------------------------


export
scalingH : {n : _} -> Num a => a -> HMatrix' n a
scalingH x = indexSet [last,last] 1 $ repeatDiag x 0

export
translationH : Num a => Vector n a -> HMatrix' n a
translationH {n} v with (viewShape v)
  _ | Shape [n] = hmatrix identity v

export
rotation2DH : Double -> HMatrix' 2 Double
rotation2DH = matrixToH . rotation2D
