module Data.NumIdr.Transform.Linear

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
Linear : Nat -> Type -> Type
Linear = Transform TLinear


export
isLinear : FieldCmp a => HMatrix' n a -> Bool
isLinear mat = isHMatrix mat && invertible (getMatrix mat)
                    && all (==0) (getTranslationVector mat)

export
fromHMatrix : FieldCmp a => HMatrix' n a -> Maybe (Linear n a)
fromHMatrix mat = if isLinear mat then Just (unsafeMkTrans mat) else Nothing

export
fromMatrix : FieldCmp a => Matrix' n a -> Maybe (Linear n a)
fromMatrix mat = if invertible mat then Just (unsafeMkTrans (matrixToH mat))
                                   else Nothing
