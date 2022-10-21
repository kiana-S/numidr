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


public export
Rotation : Nat -> Type -> Type
Rotation = Transform TRotation


-- HACK: Replace with more efficient method
export
isRotation' : FieldCmp a => Matrix' n a -> Bool
isRotation' mat = isOrthonormal mat && det mat == 1

fromMatrix : FieldCmp a => Matrix' n a -> Maybe (Rotation n a)
fromMatrix mat = if isRotation' mat then Just (unsafeMkTrans $ matrixToH mat)
                                    else Nothing

export
rotate2D : Num a => Double -> Rotation 2 Double
rotate2D = unsafeMkTrans . rotate2DH

export
rotate3DX : Num a => Double -> Rotation 3 Double
rotate3DX = unsafeMkTrans . rotate3DXH

export
rotate3DY : Num a => Double -> Rotation 3 Double
rotate3DY = unsafeMkTrans . rotate3DYH

export
rotate3DZ : Num a => Double -> Rotation 3 Double
rotate3DZ = unsafeMkTrans . rotate3DZH
