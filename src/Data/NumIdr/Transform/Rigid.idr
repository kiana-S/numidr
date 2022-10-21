module Data.NumIdr.Transform.Rigid

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
Rigid : Nat -> Type -> Type
Rigid = Transform TRigid

-- TODO: Add Rigid constructors
