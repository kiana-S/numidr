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


public export
Affine : Nat -> Type -> Type
Affine = Transform TAffine

export
isAffine : FieldCmp a => HMatrix' n a -> Bool
isAffine mat = isHMatrix mat && invertible (getMatrix mat)

export
fromHMatrix : FieldCmp a => HMatrix' n a -> Maybe (Affine n a)
fromHMatrix mat = if isAffine mat
                  then Just (unsafeMkTrans mat)
                  else Nothing
