module Data.NumIdr.Matrix

import Data.List
import Data.Vect
import Data.Permutation
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


export
permutationMatrix : {n : _} -> Num a => Permutation n -> Matrix' n a
permutationMatrix p = permuteInAxis 0 p (repeatDiag 1 0)


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
getRow r mat = rewrite sym (rangeLenZ n) in mat!!..[One r, All]

||| Return a column of the matrix as a vector.
export
getColumn : Fin n -> Matrix m n a -> Vector m a
getColumn c mat = rewrite sym (rangeLenZ m) in mat!!..[All, One c]


export
diagonal' : Matrix m n a -> Vector (minimum m n) a
diagonal' mat with (viewShape mat)
  _ | Shape [m,n] = fromFunctionNB _ (\[i] => mat!#[i,i])

export
diagonal : Matrix' n a -> Vector n a
diagonal mat with (viewShape mat)
  _ | Shape [n,n] = fromFunctionNB [n] (\[i] => mat!#[i,i])


-- TODO: throw an actual proof in here to avoid the unsafety
export
minor : Fin (S m) -> Fin (S n) -> Matrix (S m) (S n) a -> Matrix m n a
minor i j mat = believe_me $ mat!!..[Filter (/=i), Filter (/=j)]


filterInd : Num a => (Nat -> Nat -> Bool) -> Matrix m n a -> Matrix m n a
filterInd p mat with (viewShape mat)
  _ | Shape [m,n] = fromFunctionNB [m,n] (\[i,j] => if p i j then mat!#[i,j] else 0)

export
upperTriangle : Num a => Matrix m n a -> Matrix m n a
upperTriangle = filterInd (<=)

export
lowerTriangle : Num a => Matrix m n a -> Matrix m n a
lowerTriangle = filterInd (>=)

export
upperTriangleStrict : Num a => Matrix m n a -> Matrix m n a
upperTriangleStrict = filterInd (<)

export
lowerTriangleStrict : Num a => Matrix m n a -> Matrix m n a
lowerTriangleStrict = filterInd (>)


--------------------------------------------------------------------------------
-- Basic operations
--------------------------------------------------------------------------------

||| Concatenate two matrices vertically.
export
vconcat : Matrix m n a -> Matrix m' n a -> Matrix (m + m') n a
vconcat = concat 0

||| Concatenate two matrices horizontally.
export
hconcat : Matrix m n a -> Matrix m n' a -> Matrix m (n + n') a
hconcat = concat 1


export
vstack : {n : _} -> Vect m (Vector n a) -> Matrix m n a
vstack = stack 0

export
hstack : {m : _} -> Vect n (Vector m a) -> Matrix m n a
hstack = stack 1


export
swapRows : (i,j : Fin m) -> Matrix m n a -> Matrix m n a
swapRows = swapInAxis 0

export
swapColumns : (i,j : Fin n) -> Matrix m n a -> Matrix m n a
swapColumns = swapInAxis 1

export
permuteRows : Permutation m -> Matrix m n a -> Matrix m n a
permuteRows = permuteInAxis 0

export
permuteColumns : Permutation n -> Matrix m n a -> Matrix m n a
permuteColumns = permuteInAxis 1


||| Calculate the outer product of two vectors as a matrix.
export
outer : Num a => Vector m a -> Vector n a -> Matrix m n a
outer a b with (viewShape a, viewShape b)
  _ | (Shape [m], Shape [n]) = fromFunction [m,n] (\[i,j] => a!!i * b!!j)


export
trace : Num a => Matrix m n a -> a
trace = sum . diagonal'


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


--------------------------------------------------------------------------------
-- Matrix decomposition
--------------------------------------------------------------------------------


-- LU Decomposition
export
record DecompLU {0 n,a : _} (mat : Matrix' n a) where
  constructor MkLU
  lu : Matrix' n a


namespace DecompLU
  export
  lower : Num a => DecompLU {n,a} mat -> Matrix' n a
  lower (MkLU lu) with (viewShape lu)
    _ | Shape [n,n] = lowerTriangleStrict lu + identity

  export %inline
  (.lower) : Num a => DecompLU {n,a} mat -> Matrix' n a
  (.lower) = lower

  export
  upper : Num a => DecompLU {n,a} mat -> Matrix' n a
  upper (MkLU lu) = upperTriangle lu

  export %inline
  (.upper) : Num a => DecompLU {n,a} mat -> Matrix' n a
  (.upper) = upper


iterateN : (n : Nat) -> (Fin n -> a -> a) -> a -> a
iterateN 0 f x = x
iterateN 1 f x = f FZ x
iterateN (S n@(S _)) f x = iterateN n (f . FS) $ f FZ x


gaussStep : (Eq a, Neg a, Fractional a) => Fin n -> Matrix' n a -> Matrix' n a
gaussStep {n} i lu with (viewShape lu)
  _ | Shape [n,n] =
    if all (==0) $ getColumn i lu then lu else
      let diag = lu!![i,i]
          coeffs = map (/diag) $ lu!!..[StartBound (FS i), One i]
          lu' = indexSetRange [StartBound (FS i), One i]
                  coeffs lu
          pivot = lu!!..[One i, StartBound (FS i)]
          offsets = negate $ outer coeffs pivot
      in  indexUpdateRange [StartBound (FS i), StartBound (FS i)] (+offsets) lu'

export
decompLU : (Eq a, Neg a, Fractional a) => (mat : Matrix' n a) -> DecompLU mat
decompLU {n} mat with (viewShape mat)
  _ | Shape [n,n] = MkLU $ iterateN n gaussStep mat


-- LUP Decomposition
public export
record DecompLUP {0 n,a : _} (mat : Matrix' n a) where
  constructor MkLUP
  lu : Matrix' n a
  p : Permutation n
  sw : Nat

namespace DecompLUP
  export
  lower : Num a => DecompLUP {n,a} mat -> Matrix' n a
  lower (MkLUP lu p sw) with (viewShape lu)
    _ | Shape [n,n] = lowerTriangleStrict lu + identity

  export %inline
  (.lower) : Num a => DecompLUP {n,a} mat -> Matrix' n a
  (.lower) = lower

  export
  upper : Num a => DecompLUP {n,a} mat -> Matrix' n a
  upper (MkLUP lu p sw) = upperTriangle lu

  export %inline
  (.upper) : Num a => DecompLUP {n,a} mat -> Matrix' n a
  (.upper) = upper

  export
  permute : DecompLUP {n} mat -> Permutation n
  permute (MkLUP lu p sw) = p

  export %inline
  (.permute) : DecompLUP {n} mat -> Permutation n
  (.permute) = permute

  export
  numSwaps : DecompLUP {n} mat -> Nat
  numSwaps (MkLUP lu p sw) = sw

export
fromLU : DecompLU mat -> DecompLUP mat
fromLU (MkLU lu) = MkLUP lu identity 0


export
decompLUP : (Ord a, Abs a, Neg a, Fractional a) =>
            (mat : Matrix' n a) -> DecompLUP mat
decompLUP {n} mat with (viewShape mat)
  decompLUP {n=0} mat | Shape [0,0] = MkLUP mat identity 0
  decompLUP {n=S n} mat | Shape [S n,S n] =
    iterateN (S n) gaussStepSwap (MkLUP mat identity 0)
  where
    maxIndex : (s,a) -> List (s,a) -> (s,a)
    maxIndex x [] = x
    maxIndex _ [x] = x
    maxIndex x ((a,b)::(c,d)::xs) =
      if abs b < abs d then assert_total $ maxIndex x ((c,d)::xs)
                       else assert_total $ maxIndex x ((a,b)::xs)

    gaussStepSwap : Fin (S n) -> DecompLUP mat -> DecompLUP mat
    gaussStepSwap i (MkLUP lu p sw) =
      let (maxi, maxv) = mapFst head
                           (maxIndex ([0],0) $ enumerate $
                           indexSetRange [EndBound (weaken i)] 0 $ getColumn i lu)
      in  if maxi == i then MkLUP (gaussStep i lu) p sw
          else MkLUP (gaussStep i $ swapRows maxi i lu) (appendSwap maxi i p) (S sw)


--------------------------------------------------------------------------------
-- Matrix properties
--------------------------------------------------------------------------------


export
detWithLUP : (Ord a, Abs a, Neg a, Fractional a) =>
            (mat : Matrix' n a) -> DecompLUP mat -> a
detWithLUP {n} mat lup =
  (if numSwaps lup `mod` 2 == 0 then 1 else -1)
    * product (diagonal lup.lower) * product (diagonal lup.upper)

export
det : (Ord a, Abs a, Neg a, Fractional a) => Matrix' n a -> a
det {n} mat with (viewShape mat)
  det {n=0} mat | Shape [0,0] = 1
  det {n=1} mat | Shape [1,1] = mat!![0,0]
  det {n=2} mat | Shape [2,2] = let [a,b,c,d] = elements mat in a*d - b*c
  _ | Shape [n,n] = detWithLUP mat (decompLUP mat)
