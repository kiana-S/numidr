module Data.NumIdr.Transform.Isometry

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


||| An isometry is an affine transformation that preserves distance between
||| points. It encompasses translations, rotations, and reflections.
public export
Isometry : Nat -> Type -> Type
Isometry = Transform TIsometry

||| Determine if a matrix represents an isometry.
export
isIsometry : Eq a => Num a => HMatrix' n a -> Bool
isIsometry mat = isHMatrix mat && isOrthonormal' (getMatrix mat)

||| Try to construct an isometry from a homogeneous matrix.
export
fromHMatrix : Eq a => Num a => HMatrix' n a -> Maybe (Isometry n a)
fromHMatrix mat = if isIsometry mat then Just (unsafeMkTrans mat) else Nothing
