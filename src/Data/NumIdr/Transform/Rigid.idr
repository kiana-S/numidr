module Data.NumIdr.Transform.Rigid

import Data.Vect
import Data.NumIdr.Interfaces
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Matrix
import Data.NumIdr.Homogeneous
import Data.NumIdr.Transform.Point
import Data.NumIdr.Transform.Transform
import Data.NumIdr.Transform.Rotation

%default total


||| A rigid transform encodes a (proper) rigid transformation, also known as a
||| rototranslation.
public export
Rigid : Nat -> Type -> Type
Rigid = Transform TRigid

-- TODO: Add Rigid constructors

||| Determine if a homogeneous matrix represents a rigid transform.
export
isRigid : FieldCmp a => HMatrix' n a -> Bool
isRigid mat = isHMatrix mat && isRotation' (getMatrix mat)

export
fromHMatrix : FieldCmp a => HMatrix' n a -> Maybe (Rigid n a)
fromHMatrix mat = if isRigid mat then Just (unsafeMkTrans mat) else Nothing


export
rigid2D : Vector 2 Double -> Double -> Rigid 2 Double
rigid2D v a = setTranslation v (rotate2D a)


||| Construct a 3D rigid transform representing an observer standing at `orig`
||| and facing towards `target`.
|||
||| @ orig The origin point, i.e. the point that the origin is mapped to.
||| @ target The point that the z-axis is directed towards.
||| @ up The vertical direction, the direction that the y-axis faces.
export
faceTowards : (orig, target : Point 3 Double) -> (up : Vector 3 Double)
                -> Rigid 3 Double
faceTowards orig target up = setTranslation (toVector orig)
                                            (faceTowards (orig -. target) up)
