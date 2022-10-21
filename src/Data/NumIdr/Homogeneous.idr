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


||| Convert a vector to a homogeneous vector.
export
vectorToH : Num a => Vector n a -> HVector n a
vectorToH v = rewrite plusCommutative 1 n in v ++ vector [1]

||| Convert a vector to a homogeneous vector that ignores the translation
||| component of homogeneous matrices.
export
vectorToHLinear : Num a => Vector n a -> HVector n a
vectorToHLinear v = rewrite plusCommutative 1 n in v ++ vector [0]

||| Construct a homogeneous vector given its coordinates.
export
hvector : Num a => Vect n a -> HVector n a
hvector v = rewrite plusCommutative 1 n in vector (v ++ [1])

||| Construct a homogeneous vector that ignores translations given its
||| coordinates.
export
hvectorLinear : Num a => Vect n a -> HVector n a
hvectorLinear v = rewrite plusCommutative 1 n in vector (v ++ [0])


||| Extract a normal vector from a homogeneous vector.
export
fromHomogeneous : HVector n a -> Vector n a
fromHomogeneous {n} v with (viewShape v)
  _ | Shape [S n] = resizeLTE [n] v {ok = [lteSuccRight reflexive]}


||| Construct a homogeneous matrix given a matrix and a translation vector.
export
hmatrix : Num a => Matrix m n a -> Vector m a -> HMatrix m n a
hmatrix {m,n} mat tr with (viewShape mat)
  _ | Shape [m,n] = indexSet [last,last] 1 $
                    resize [S m, S n] 0 $
                    mat `hconcat` reshape
                      {ok = sym $ multOneRightNeutral _} [m,1] tr

||| Convert a regular matrix to a homogeneous matrix.
export
matrixToH : Num a => Matrix m n a -> HMatrix m n a
matrixToH {m,n} mat with (viewShape mat)
  _ | Shape [m,n] = indexSet [last,last] 1 $ resize [S m, S n] 0 mat


||| Determine if a matrix fits the pattern of a homogeneous matrix.
export
isHMatrix : Eq a => Num a => Matrix m n a -> Bool
isHMatrix {m,n} mat with (viewShape mat)
  isHMatrix {m=Z,n} mat | Shape [Z,n] = False
  isHMatrix {m=S m,n=Z} mat | Shape [S m,Z] = False
  isHMatrix {m=S m,n=S n} mat | Shape [S m,S n] =
    getRow last mat == resize _ 1 (zeros [n])


||| Get the regular matrix component of a homogeneous matrix.
export
getMatrix : HMatrix m n a -> Matrix m n a
getMatrix {m,n} mat with (viewShape mat)
  _ | Shape [S m, S n] = resizeLTE [m,n] mat
                          {ok = [lteSuccRight reflexive,lteSuccRight reflexive]}

||| Get the translation vector from a homogeneous matrix.
export
getTranslationVector : HMatrix m n a -> Vector m a
getTranslationVector {m,n} mat with (viewShape mat)
  _ | Shape [S m, S n] = resizeLTE [m] {ok = [lteSuccRight reflexive]} $
                          getColumn last mat


--------------------------------------------------------------------------------
-- Constructors of homogeneous matrices
--------------------------------------------------------------------------------


||| Construct a homogeneous matrix that scales a vector by the input.
export
scalingH : {n : _} -> Num a => a -> HMatrix' n a
scalingH x = indexSet [last,last] 1 $ repeatDiag x 0

||| Construct a homogeneous matrix that translates by the given vector.
export
translationH : Num a => Vector n a -> HMatrix' n a
translationH {n} v with (viewShape v)
  _ | Shape [n] = hmatrix identity v

||| Construct a 2D homogeneous matrix that rotates by the given angle (in radians).
export
rotate2DH : Double -> HMatrix' 2 Double
rotate2DH = matrixToH . rotate2D

||| Construct a 3D homogeneous matrix that rotates around the x-axis.
export
rotate3DXH : Double -> HMatrix' 3 Double
rotate3DXH = matrixToH . rotate3DX

||| Construct a 3D homogeneous matrix that rotates around the y-axis.
export
rotate3DYH : Double -> HMatrix' 3 Double
rotate3DYH = matrixToH . rotate3DY

||| Construct a 3D homogeneous matrix that rotates around the z-axis.
export
rotate3DZH : Double -> HMatrix' 3 Double
rotate3DZH = matrixToH . rotate3DZ
