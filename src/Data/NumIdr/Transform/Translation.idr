module Data.NumIdr.Transform.Translation

import Data.Vect
import Data.NumIdr.Multiply
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Transform.Point

%default total


export
record Translation n a where
  constructor MkTrl
  offset : Vector n a

export
fromVector : Vector n a -> Translation n a
fromVector = MkTrl


export
Cast a b => Cast (Translation n a) (Translation n b) where
  cast (MkTrl v) = MkTrl (cast v)

export
Num a => Mult (Translation n a) (Translation n a) (Translation n a) where
  MkTrl a *. MkTrl b = MkTrl (zipWith (+) a b)

export
{n : _} -> Num a => MultMonoid (Translation n a) where
  identity = MkTrl $ zeros [n]

export
{n : _} -> Neg a => MultGroup (Translation n a) where
  inverse (MkTrl v) = MkTrl (-v)
