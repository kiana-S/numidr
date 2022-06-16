module Data.NumIdr.Matrix

import Data.Vect
import Data.NumIdr.Multiply
import public Data.NumIdr.Array
import Data.NumIdr.Vector

%default total


public export
Matrix : Nat -> Nat -> Type -> Type
Matrix m n = Array [m,n]

public export
Matrix' : Nat -> Type -> Type
Matrix' n = Matrix n n


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
   (\[i,j] => if i `eq` j then d else o)
  where
    eq : {0 m,n : Nat} -> Fin m -> Fin n -> Bool
    eq FZ FZ = True
    eq (FS x) (FS y) = eq x y
    eq FZ (FS _) = False
    eq (FS _) FZ = False

export
fromDiag : {m, n : _} -> (diag : Vect (minimum m n) a) -> (other : a) -> Matrix m n a
fromDiag ds o = fromFunction [m,n] (\[i,j] => maybe o (`index` ds) $ i `eq` j)
  where
    eq : {0 m,n : Nat} -> Fin m -> Fin n -> Maybe (Fin (minimum m n))
    eq FZ FZ = Just FZ
    eq (FS x) (FS y) = map FS (eq x y)
    eq FZ (FS _) = Nothing
    eq (FS _) FZ = Nothing


export
identity : Num a => {n : _} -> Matrix n n a
identity = repeatDiag 1 0


export
scaling : Num a => {n : _} -> a -> Matrix n n a
scaling x = repeatDiag x 0

export
rotation2D : Double -> Matrix' 2 Double
rotation2D a = matrix [[cos a, - sin a], [sin a, cos a]]


--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------


export
index : Fin m -> Fin n -> Matrix m n a -> a
index m n = index [m,n]

export
indexMaybe : Nat -> Nat -> Matrix m n a -> Maybe a
indexMaybe m n = indexMaybe [m,n]


export
getRow : Fin m -> Matrix m n a -> Vector n a
getRow r mat = rewrite sym (minusZeroRight n) in indexRange [One r, All] mat

export
getColumn : Fin n -> Matrix m n a -> Vector m a
getColumn c mat = rewrite sym (minusZeroRight m) in indexRange [All, One c] mat


--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

export
vconcat : Matrix m n a -> Matrix m' n a -> Matrix (m + m') n a
vconcat = concat 0

export
hconcat : Matrix m n a -> Matrix m n' a -> Matrix m (n + n') a
hconcat = concat 1


export
kronecker : Num a => Vector m a -> Vector n a -> Matrix m n a
kronecker a b with (viewShape a, viewShape b)
  _ | (Shape [m], Shape [n]) = fromFunction [m,n] (\[i,j] => index i a * index j b)
