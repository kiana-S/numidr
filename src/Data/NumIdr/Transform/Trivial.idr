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


||| A trivial transform is a transform that must leave all points unchanged.
||| This transform type only exists so that `linearize` can take a translation
||| as input.
public export
Trivial : Nat -> Type -> Type
Trivial = Transform TTrivial


||| Determine if a homogeneous matrix is trivial.
export
isTrivial : Eq a => Num a => HMatrix' n a -> Bool
isTrivial {n} mat with (viewShape mat)
  _ | Shape [S n,S n] = mat == identity
