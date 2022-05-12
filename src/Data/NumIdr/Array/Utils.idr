module Data.NumIdr.Array.Utils

import Data.NumIdr.Array.Array


export
zeros : Num a => (s : Vect rk Nat) -> Array s a
zeros = constant 0

export
ones : Num a => (s : Vect rk Nat) -> Array s a
ones = constant 1
