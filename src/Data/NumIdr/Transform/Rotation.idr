module Data.NumIdr.Transform.Rotation

import Data.Vect
import Data.NumIdr.Interfaces
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Matrix
import Data.NumIdr.Homogeneous
import Data.NumIdr.Transform.Point
import Data.NumIdr.Transform.Transform
import Data.NumIdr.Transform.Orthonormal

%default total


||| A transform that contains a rotation.
public export
Rotation : Nat -> Type -> Type
Rotation = Transform TRotation


||| Determine if a matrix represents a rotation.
-- HACK: Replace with more efficient method
export
isRotation' : FieldCmp a => Matrix' n a -> Bool
isRotation' mat = isOrthonormal' mat && det mat == 1

||| Try to constuct a rotation from a matrix.
fromMatrix : FieldCmp a => Matrix' n a -> Maybe (Rotation n a)
fromMatrix mat = if isRotation' mat then Just (unsafeMkTrans $ matrixToH mat)
                                    else Nothing

||| Determine if a homogeneous matrix represents a rotation.
export
isRotation : FieldCmp a => HMatrix' n a -> Bool
isRotation {n} mat with (viewShape mat)
  _ | Shape [S n, S n] = isHMatrix mat && all (==0) (mat !!.. [EndBound last, One last])

||| Construct a 2D rotation that rotates by the given angle (in radians).
export
rotate2D : Num a => Double -> Rotation 2 Double
rotate2D = unsafeMkTrans . rotate2DH


--------------------------------------------------------------------------------
-- 3D rotations
--------------------------------------------------------------------------------


||| Construct a 3D rotation around the x-axis.
export
rotate3DX : Double -> Rotation 3 Double
rotate3DX = unsafeMkTrans . rotate3DXH

||| Construct a 3D rotation around the y-axis.
export
rotate3DY : Double -> Rotation 3 Double
rotate3DY = unsafeMkTrans . rotate3DYH

||| Construct a 3D rotation around the z-axis.
export
rotate3DZ : Double -> Rotation 3 Double
rotate3DZ = unsafeMkTrans . rotate3DZH


||| Construct a rotation representing an observer facing towards `dir`.
|||
||| @ dir The facing direction, aligned with the z-axis.
||| @ up The vertical direction, the direction that the y-axis faces.
export
faceTowards : (dir, up : Vector 3 Double) -> Rotation 3 Double
faceTowards dir up = let z = normalize dir
                         x = normalize (up `cross` z)
                         y = normalize (z `cross` x)
                     in  unsafeMkTrans $ matrixToH $ hstack [x,y,z]
