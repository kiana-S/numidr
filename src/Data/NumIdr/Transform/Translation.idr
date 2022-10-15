module Data.NumIdr.Transform.Translation

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
Translation : Nat -> Type -> Type
Translation = Transform TTranslation


export
isTranslation : (Eq a, Num a) => HMatrix' n a -> Bool
isTranslation {n} mat with (viewShape mat)
  _ | Shape [S n,S n] = isHMatrix mat && getMatrix mat == identity

export
fromVector : Num a => Vector n a -> Translation n a
fromVector v = unsafeMkTrans (translationH v)

export
fromHMatrix : (Eq a, Num a) => HMatrix' n a -> Maybe (Translation n a)
fromHMatrix mat = if isTranslation mat then Just (unsafeMkTrans mat) else Nothing
