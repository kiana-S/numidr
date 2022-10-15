module Data.NumIdr.Transform.Orthonormal

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
Orthonormal : Nat -> Type -> Type
Orthonormal = Transform TOrthonormal


export
isOrthonormal : Eq a => Num a => Matrix' n a -> Bool
isOrthonormal {n} mat with (viewShape mat)
  _ | Shape [n,n] = identity == fromFunction [n,n] (\[i,j] => getColumn i mat `dot` getColumn j mat)

export
fromMatrix : Eq a => Num a => Matrix' n a -> Maybe (Orthonormal n a)
fromMatrix mat = if isOrthonormal mat then Just (unsafeMkTrans (matrixToH mat))
                                     else Nothing


export
reflect : {n : _} -> Neg a => Fin n -> Orthonormal n a
reflect i = unsafeMkTrans $ indexSet [weaken i,weaken i] (-1) identity

export
reflectX : {n : _} -> Neg a => Orthonormal (1 + n) a
reflectX = reflect 0

export
reflectY : {n : _} -> Neg a => Orthonormal (2 + n) a
reflectY = reflect 1

export
reflectZ : {n : _} -> Neg a => Orthonormal (3 + n) a
reflectZ = reflect 2


export
reflectNormal : (Neg a, Fractional a) => Vector n a -> Orthonormal n a
reflectNormal {n} v with (viewShape v)
  _ | Shape [n] = unsafeMkTrans $ matrixToH $ (identity - (2 / normSq v) *. outer v v)
