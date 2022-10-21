module Data.NumIdr.Transform.Trivial

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
Trivial : Nat -> Type -> Type
Trivial = Transform TTrivial


export
isTrivial : Eq a => Num a => HMatrix' n a -> Bool
isTrivial {n} mat with (viewShape mat)
  _ | Shape [S n,S n] = mat == identity
