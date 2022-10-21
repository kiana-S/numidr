module Data.NumIdr.Transform.Affine

import Data.Vect
import Data.NumIdr.Interfaces
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Matrix
import Data.NumIdr.Homogeneous
import Data.NumIdr.Transform.Point
import Data.NumIdr.Transform.Transform

%default total


||| An affine transform can contain any invertible affine map.
public export
Affine : Nat -> Type -> Type
Affine = Transform TAffine

||| Determine if a homogeneous matrix represents an affine transform
||| (i.e. is invertible).
export
isAffine : FieldCmp a => HMatrix' n a -> Bool
isAffine mat = isHMatrix mat && invertible (getMatrix mat)


||| Try to construct an affine transform from a homogeneous matrix.
export
fromHMatrix : FieldCmp a => HMatrix' n a -> Maybe (Affine n a)
fromHMatrix mat = if isAffine mat
                  then Just (unsafeMkTrans mat)
                  else Nothing
