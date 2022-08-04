module Data.NumIdr.Matrix

import Data.Vect
import Data.NumIdr.Multiply
import public Data.NumIdr.Array
import Data.NumIdr.Vector

%default total


||| A matrix is a rank-2 array.
public export
Matrix : Nat -> Nat -> Type -> Type
Matrix m n = Array [m,n]

||| A synonym for a square matrix with dimensions of length `n`.
public export
Matrix' : Nat -> Type -> Type
Matrix' n = Matrix n n


--------------------------------------------------------------------------------
-- Matrix constructors
--------------------------------------------------------------------------------


||| Construct a matrix with the given order and elements.
export
matrix' : {m, n : _} -> Order -> Vect m (Vect n a) -> Matrix m n a
matrix' ord x = array' [m,n] ord x

||| Construct a matrix with the given elements.
export
matrix : {m, n : _} -> Vect m (Vect n a) -> Matrix m n a
matrix = matrix' COrder


||| Construct a matrix with a specific value along the diagonal.
|||
||| @ diag  The value to repeat along the diagonal
||| @ other The value to repeat elsewhere
export
repeatDiag : {m, n : _} -> (diag, other : a) -> Matrix m n a
repeatDiag d o = fromFunctionNB [m,n]
   (\[i,j] => if i == j then d else o)

||| Construct a matrix given its diagonal elements.
|||
||| @ diag  The elements of the matrix's diagonal
||| @ other The value to repeat elsewhere
export
fromDiag : {m, n : _} -> (diag : Vect (minimum m n) a) -> (other : a) -> Matrix m n a
fromDiag ds o = fromFunction [m,n] (\[i,j] => maybe o (`index` ds) $ i `eq` j)
  where
    eq : {0 m,n : Nat} -> Fin m -> Fin n -> Maybe (Fin (minimum m n))
    eq FZ FZ = Just FZ
    eq (FS x) (FS y) = map FS (eq x y)
    eq FZ (FS _) = Nothing
    eq (FS _) FZ = Nothing


||| Construct the matrix that scales a vector by the given value.
export
scaling : {n : _} -> Num a => a -> Matrix' n a
scaling x = repeatDiag x 0

||| Calculate the rotation matrix of an angle.
export
rotation2D : Double -> Matrix' 2 Double
rotation2D a = matrix [[cos a, - sin a], [sin a, cos a]]


--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------


||| Index the matrix at the given coordinates.
export
index : Fin m -> Fin n -> Matrix m n a -> a
index m n = index [m,n]

||| Index the matrix at the given coordinates, returning `Nothing` if the
||| coordinates are out of bounds.
export
indexNB : Nat -> Nat -> Matrix m n a -> Maybe a
indexNB m n = indexNB [m,n]


||| Return a row of the matrix as a vector.
export
getRow : Fin m -> Matrix m n a -> Vector n a
getRow r mat = rewrite sym (minusZeroRight n) in indexRange [One r, All] mat

||| Return a column of the matrix as a vector.
export
getColumn : Fin n -> Matrix m n a -> Vector m a
getColumn c mat = rewrite sym (minusZeroRight m) in indexRange [All, One c] mat


export
diagonal' : Matrix m n a -> Vector (minimum m n) a
diagonal' mat with (viewShape mat)
  _ | Shape [m,n] = fromFunctionNB _ (\[i] => mat!#[i,i])

export
diagonal : Matrix' n a -> Vector n a
diagonal mat with (viewShape mat)
  _ | Shape [n,n] = fromFunctionNB [n] (\[i] => mat!#[i,i])


--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

||| Concatenate two matrices vertically.
export
vconcat : Matrix m n a -> Matrix m' n a -> Matrix (m + m') n a
vconcat = concat 0

||| Concatenate two matrices horizontally.
export
hconcat : Matrix m n a -> Matrix m n' a -> Matrix m (n + n') a
hconcat = concat 1


||| Calculate the outer product of two vectors as a matrix.
export
outer : Num a => Vector m a -> Vector n a -> Matrix m n a
outer a b with (viewShape a, viewShape b)
  _ | (Shape [m], Shape [n]) = fromFunction [m,n] (\[i,j] => a!!i * b!!j)


export
trace : Num a => Matrix m n a -> a
trace = sum . diagonal'


export
det : Neg a => Matrix' n a -> a
det {n} mat with (viewShape mat)
  det {n=0} mat | Shape [0,0] = 1
  det {n=1} mat | Shape [1,1] = mat!![0,0]
  det {n=2} mat | Shape [2,2] = let [a,b,c,d] = elements mat in a * d - b * c
  _ | Shape [n,n] = sum $
      map (\(p,s) => s * product (map (\i => indexUnsafe [finToNat i,index i p] mat) range))
      $ permutations n
  where
    -- Compute all permutations
    permutations : (n : Nat) -> List (Vect n Nat, a)
    permutations Z = [([], 1)]
    permutations (S n) = do (p,s) <- permutations n
                            i <- toList $ range {len=S n}
                            pure (insertAt i Z (map S p),
                              if (finToNat i) `mod` 2 == 0 then s else -s)


--------------------------------------------------------------------------------
-- Matrix multiplication
--------------------------------------------------------------------------------


export
Num a => Mult (Matrix m n a) (Vector n a) (Vector m a) where
  mat *. v with (viewShape mat)
    _ | Shape [m,n] = fromFunction [m]
      (\[i] => sum $ map (\j => mat!![i,j] * v!!j) range)

export
Num a => Mult (Matrix m n a) (Matrix n p a) (Matrix m p a) where
  m1 *. m2 with (viewShape m1, viewShape m2)
    _ | (Shape [m,n], Shape [n,p]) = fromFunction [m,p]
      (\[i,j] => sum $ map (\k => m1!![i,k] * m2!![k,j]) range)

export
{n : _} -> Num a => MultMonoid (Matrix' n a) where
  identity = repeatDiag 1 0


export
{n : _} -> Neg a => Fractional a => MultGroup (Matrix' n a) where
  inverse {n=0} mat = mat
  inverse {n=1} mat = recip mat
  inverse {n=2} mat = let [a,b,c,d] = elements mat
                      in recip (det mat) *. matrix [[d,-b],[-c,a]]
  inverse {n} mat = ?matrixInverse
