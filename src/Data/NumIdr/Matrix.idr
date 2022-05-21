module Data.NumIdr.Matrix

import Data.Vect
import public Data.NumIdr.Array

%default total


public export
Matrix : Nat -> Nat -> Type -> Type
Matrix m n = Array [m,n]



--------------------------------------------------------------------------------
-- Matrix constructors
--------------------------------------------------------------------------------


export
matrix' : {m, n : _} -> Order -> Vect m (Vect n a) -> Matrix m n a
matrix' ord x = array' [m,n] ord x

export
matrix : {m, n : _} -> Vect m (Vect n a) -> Matrix m n a
matrix = matrix' COrder


export
repeatDiag : {m, n : _} -> (diag, other : a) -> Matrix m n a
repeatDiag d o = fromFunction [m,n]
   (\[i,j] => if finToNat i == finToNat j then d else o)

export
identity : Num a => {n : _} -> Matrix n n a
identity = repeatDiag 1 0




--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------


export
index : Fin m -> Fin n -> Matrix m n a -> a
index m n = index [m,n]


--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------
