module Data.NumIdr.Transform.Rotation

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
Rotation : Nat -> Type -> Type
Rotation = Transform TRotation


export
isRotation' : Matrix' n a -> Bool
isRotation' mat =
