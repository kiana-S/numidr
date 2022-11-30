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


||| An orthonormal transform is one that contains an orthonormal matrix,
||| also known as an improper rotation or rotoreflection.
public export
Orthonormal : Nat -> Type -> Type
Orthonormal = Transform TOrthonormal


||| Determine if a matrix represents an orthonormal transform.
export
isOrthonormal' : Eq a => Num a => Matrix' n a -> Bool
isOrthonormal' {n} mat with (viewShape mat)
  _ | Shape [n,n] = identity == fromFunction [n,n] (\[i,j] => getColumn i mat `dot` getColumn j mat)

||| Try to construct an orthonormal transform from a matrix.
export
fromMatrix : Eq a => Num a => Matrix' n a -> Maybe (Orthonormal n a)
fromMatrix mat = if isOrthonormal' mat then Just (unsafeMkTrans (matrixToH mat))
                                       else Nothing


--------------------------------------------------------------------------------
-- Reflections
--------------------------------------------------------------------------------


||| Construct an orthonormal transform that reflects a particular coordinate.
export
reflect : {n : _} -> Neg a => Fin n -> Orthonormal n a
reflect = unsafeMkTrans . reflectH

||| The orthonormal transform that reflects on the x-coordinate (first coordinate).
export
reflectX : {n : _} -> Neg a => Orthonormal (1 + n) a
reflectX = reflect 0

||| The orthonormal transform that reflects on the y-coordinate (second coordinate).
export
reflectY : {n : _} -> Neg a => Orthonormal (2 + n) a
reflectY = reflect 1

||| The orthonormal transform that reflects on the z-coordinate (third coordinate).
export
reflectZ : {n : _} -> Neg a => Orthonormal (3 + n) a
reflectZ = reflect 2


||| Construct an orthonormal transform that reflects along a hyperplane of the
||| given normal vector. The input does not have to be a unit vector.
export
reflectNormal : (Neg a, Fractional a) => Vector n a -> Orthonormal n a
reflectNormal {n} v with (viewShape v)
  _ | Shape [n] = unsafeMkTrans $ matrixToH $ identity - (2 / normSq v) *. outer v v
