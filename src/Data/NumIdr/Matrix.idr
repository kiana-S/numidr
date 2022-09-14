module Data.NumIdr.Matrix

import Data.List
import Data.Vect
import Data.Permutation
import Data.NumIdr.Interfaces
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


||| Construct a permutation matrix based on the given permutation.
export
permuteM : {n : _} -> Num a => Permutation n -> Matrix' n a
permuteM p = permuteInAxis 0 p (repeatDiag 1 0)


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


||| Return the diagonal elements of the matrix as a vector.
export
diagonal' : Matrix m n a -> Vector (minimum m n) a
diagonal' {m,n} mat with (viewShape mat)
  _ | Shape [m,n] = fromFunctionNB _ (\[i] => mat!#[i,i])

||| Return the diagonal elements of the matrix as a vector.
export
diagonal : Matrix' n a -> Vector n a
diagonal {n} mat with (viewShape mat)
  _ | Shape [n,n] = fromFunctionNB [n] (\[i] => mat!#[i,i])


||| Return a minor of the matrix, i.e. the matrix formed by removing a
||| single row and column.
export
-- TODO: throw an actual proof in here to avoid the unsafety
minor : Fin (S m) -> Fin (S n) -> Matrix (S m) (S n) a -> Matrix m n a
minor i j mat = believe_me $ mat!!..[Filter (/=i), Filter (/=j)]


filterInd : Num a => (Nat -> Nat -> Bool) -> Matrix m n a -> Matrix m n a
filterInd {m,n} p mat with (viewShape mat)
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

||| Stack row vectors to form a matrix.
export
vstack : {n : _} -> Vect m (Vector n a) -> Matrix m n a
vstack = stack 0

||| Stack column vectors to form a matrix.
export
hstack : {m : _} -> Vect n (Vector m a) -> Matrix m n a
hstack = stack 1


||| Swap two rows of a matrix.
export
swapRows : (i,j : Fin m) -> Matrix m n a -> Matrix m n a
swapRows = swapInAxis 0

||| Swap two columns of a matrix.
export
swapColumns : (i,j : Fin n) -> Matrix m n a -> Matrix m n a
swapColumns = swapInAxis 1

||| Permute the rows of a matrix.
export
permuteRows : Permutation m -> Matrix m n a -> Matrix m n a
permuteRows = permuteInAxis 0

||| Permute the columns of a matrix.
export
permuteColumns : Permutation n -> Matrix m n a -> Matrix m n a
permuteColumns = permuteInAxis 1


||| Calculate the outer product of two vectors as a matrix.
export
outer : Num a => Vector m a -> Vector n a -> Matrix m n a
outer {m,n} a b with (viewShape a, viewShape b)
  _ | (Shape [m], Shape [n]) = fromFunction [m,n] (\[i,j] => a!!i * b!!j)


||| Calculate the trace of a matrix, i.e. the sum of its diagonal elements.
export
trace : Num a => Matrix m n a -> a
trace = sum . diagonal'


--------------------------------------------------------------------------------
-- Matrix multiplication
--------------------------------------------------------------------------------


export
Num a => Mult (Matrix m n a) (Vector n a) (Vector m a) where
  (*.) {m,n} mat v with (viewShape mat)
    _ | Shape [m,n] = fromFunction [m]
      (\[i] => sum $ map (\j => mat!![i,j] * v!!j) range)

export
Num a => Mult (Matrix m n a) (Matrix n p a) (Matrix m p a) where
  (*.) {m,n,p} m1 m2 with (viewShape m1, viewShape m2)
    _ | (Shape [m,n], Shape [n,p]) = fromFunction [m,p]
      (\[i,j] => sum $ map (\k => m1!![i,k] * m2!![k,j]) range)

export
{n : _} -> Num a => MultMonoid (Matrix' n a) where
  identity = repeatDiag 1 0


--------------------------------------------------------------------------------
-- Matrix decomposition
--------------------------------------------------------------------------------


||| The LU decomposition of a matrix.
|||
||| LU decomposition factors a matrix A into two matrices: a lower triangular
||| matrix L, and an upper triangular matrix U, such that A = LU.
export
record DecompLU {0 m,n,a : _} (mat : Matrix m n a) where
  constructor MkLU
  -- The lower and upper triangular matrix elements are stored
  -- together for efficiency reasons
  lu : Matrix m n a


namespace DecompLU
  ||| The lower triangular matrix L of the LU decomposition.
  export
  lower : Num a => DecompLU {m,n,a} mat -> Matrix m (minimum m n) a
  lower {m,n} (MkLU lu) with (viewShape lu)
    _ | Shape [m,n] = fromFunctionNB _ (\[i,j] =>
      case compare i j of
        LT => 0
        EQ => 1
        GT => lu!#[i,j])

  ||| The lower triangular matrix L of the LU decomposition.
  export %inline
  (.lower) : Num a => DecompLU {m,n,a} mat -> Matrix m (minimum m n) a
  (.lower) = lower

  ||| The lower triangular matrix L of the LU decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export
  lower' : Num a => {0 mat : Matrix' n a} -> DecompLU mat -> Matrix' n a
  lower' lu = rewrite cong (\i => Matrix n i a) $ sym (minimumIdempotent n)
              in lower lu

  ||| The lower triangular matrix L of the LU decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export %inline
  (.lower') : Num a => {0 mat : Matrix' n a} -> DecompLU mat -> Matrix' n a
  (.lower') = lower'

  ||| The upper triangular matrix U of the LU decomposition.
  export
  upper : Num a => DecompLU {m,n,a} mat -> Matrix (minimum m n) n a
  upper {m,n} (MkLU lu) with (viewShape lu)
    _ | Shape [m,n] = fromFunctionNB _ (\[i,j] =>
      if i <= j then lu!#[i,j] else 0)

  ||| The upper triangular matrix U of the LU decomposition.
  export %inline
  (.upper) : Num a => DecompLU {m,n,a} mat -> Matrix (minimum m n) n a
  (.upper) = upper

  ||| The upper triangular matrix U of the LU decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export
  upper' : Num a => {0 mat : Matrix' n a} -> DecompLU mat -> Matrix' n a
  upper' lu = rewrite cong (\i => Matrix i n a) $ sym (minimumIdempotent n)
              in upper lu

  ||| The upper triangular matrix U of the LU decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export %inline
  (.upper') : Num a => {0 mat : Matrix' n a} -> DecompLU mat -> Matrix' n a
  (.upper') = upper'


minWeakenLeft : {m,n : _} -> Fin (minimum m n) -> Fin m
minWeakenLeft x = weakenLTE x $ minLTE m n
  where
    minLTE : (m,n : _) -> minimum m n `LTE` m
    minLTE Z n = LTEZero
    minLTE (S m) Z = LTEZero
    minLTE (S m) (S n) = LTESucc (minLTE m n)

minWeakenRight : {m,n : _} -> Fin (minimum m n) -> Fin n
minWeakenRight x = weakenLTE x $ minLTE m n
  where
    minLTE : (m,n : _) -> minimum m n `LTE` n
    minLTE Z n = LTEZero
    minLTE (S m) Z = LTEZero
    minLTE (S m) (S n) = LTESucc (minLTE m n)


iterateN : (n : Nat) -> (Fin n -> a -> a) -> a -> a
iterateN 0 f x = x
iterateN 1 f x = f FZ x
iterateN (S n@(S _)) f x = iterateN n (f . FS) $ f FZ x


||| Perform a single step of Gaussian elimination on the `i`-th row and column.
gaussStep : {m,n : _} -> Field a =>
            Fin (minimum m n) -> Matrix m n a -> Matrix m n a
gaussStep i lu =
    if all (==0) $ getColumn (minWeakenRight i) lu then lu else
      let ir = minWeakenLeft i
          ic = minWeakenRight i
          diag = lu!![ir,ic]
          coeffs = map (/diag) $ lu!!..[StartBound (FS ir), One ic]
          lu' = indexSetRange [StartBound (FS ir), One ic] coeffs lu
          pivot = lu!!..[One ir, StartBound (FS ic)]
          offsets = outer coeffs pivot
      in  indexUpdateRange [StartBound (FS ir), StartBound (FS ic)]
            (flip (-) offsets) lu'

||| Calculate the LU decomposition of a matrix, returning `Nothing` if one
||| does not exist.
export
decompLU : Field a => (mat : Matrix m n a) -> Maybe (DecompLU mat)
decompLU {m,n} mat with (viewShape mat)
  _ | Shape [m,n] = map MkLU $ iterateN (minimum m n) (\i => (>>= gaussStepMaybe i)) (Just mat)
  where
    gaussStepMaybe : Fin (minimum m n) -> Matrix m n a -> Maybe (Matrix m n a)
    gaussStepMaybe i mat = if mat!#[cast i,cast i] == 0 then Nothing
                           else Just (gaussStep i mat)


||| The LUP decomposition of a matrix.
|||
||| LUP decomposition is similar to LU decomposition, but the matrix may have
||| its rows permuted before being factored. More formally, an LUP decomposition
||| of a matrix A consists of a lower triangular matrix L, an upper triangular
||| matrix U, and a permutation matrix P, such that PA = LU.
export
record DecompLUP {0 m,n,a : _} (mat : Matrix m n a) where
  constructor MkLUP
  lu : Matrix m n a
  p : Permutation m
  sw : Nat

namespace DecompLUP
  ||| The lower triangular matrix L of the LUP decomposition.
  export
  lower : Num a => DecompLUP {m,n,a} mat -> Matrix m (minimum m n) a
  lower {m,n} (MkLUP lu _ _) with (viewShape lu)
    _ | Shape [m,n] = fromFunctionNB _ (\[i,j] =>
      case compare i j of
        LT => 0
        EQ => 1
        GT => lu!#[i,j])

  ||| The lower triangular matrix L of the LUP decomposition.
  export %inline
  (.lower) : Num a => DecompLUP {m,n,a} mat -> Matrix m (minimum m n) a
  (.lower) = lower

  ||| The lower triangular matrix L of the LUP decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export
  lower' : Num a => {0 mat : Matrix' n a} -> DecompLUP mat -> Matrix' n a
  lower' lu = rewrite cong (\i => Matrix n i a) $ sym (minimumIdempotent n)
              in lower lu

  ||| The lower triangular matrix L of the LUP decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export %inline
  (.lower') : Num a => {0 mat : Matrix' n a} -> DecompLUP mat -> Matrix' n a
  (.lower') = lower'

  ||| The upper triangular matrix U of the LUP decomposition.
  export
  upper : Num a => DecompLUP {m,n,a} mat -> Matrix (minimum m n) n a
  upper {m,n} (MkLUP lu _ _) with (viewShape lu)
    _ | Shape [m,n] = fromFunctionNB _ (\[i,j] =>
      if i <= j then lu!#[i,j] else 0)

  ||| The upper triangular matrix U of the LUP decomposition.
  export %inline
  (.upper) : Num a => DecompLUP {m,n,a} mat -> Matrix (minimum m n) n a
  (.upper) = upper

  ||| The upper triangular matrix U of the LUP decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export
  upper' : Num a => {0 mat : Matrix' n a} -> DecompLUP mat -> Matrix' n a
  upper' lu = rewrite cong (\i => Matrix i n a) $ sym (minimumIdempotent n)
              in upper lu

  ||| The upper triangular matrix U of the LUP decomposition.
  |||
  ||| This accessor is intended to be used for square matrix decompositions.
  export %inline
  (.upper') : Num a => {0 mat : Matrix' n a} -> DecompLUP mat -> Matrix' n a
  (.upper') = upper'

  ||| The row permutation of the LUP decomposition.
  export
  permute : DecompLUP {m} mat -> Permutation m
  permute (MkLUP lu p sw) = p

  ||| The row permutation of the LUP decomposition.
  export %inline
  (.permute) : DecompLUP {m} mat -> Permutation m
  (.permute) = permute

  ||| The number of swaps in the permutation of the LUP decomposition.
  |||
  ||| This is stored along with the permutation in order to increase the
  ||| efficiency of certain algorithms.
  export
  numSwaps : DecompLUP mat -> Nat
  numSwaps (MkLUP lu p sw) = sw


||| Convert an LU decomposition into an LUP decomposition.
export
fromLU : DecompLU mat -> DecompLUP mat
fromLU (MkLU lu) = MkLUP lu identity 0

||| Calculate the LUP decomposition of a matrix.
export
decompLUP : FieldCmp a => (mat : Matrix m n a) -> DecompLUP mat
decompLUP {m,n} mat with (viewShape mat)
  decompLUP {m=0,n} mat | Shape [0,n] = MkLUP mat identity 0
  decompLUP {m=S m,n=0} mat | Shape [S m,0] = MkLUP mat identity 0
  decompLUP {m=S m,n=S n} mat | Shape [S m,S n] =
    iterateN (S $ minimum m n) gaussStepSwap (MkLUP mat identity 0)
  where
    maxIndex : (s,a) -> List (s,a) -> (s,a)
    maxIndex x [] = x
    maxIndex _ [x] = x
    maxIndex x ((a,b)::(c,d)::xs) =
      if abslt b d then assert_total $ maxIndex x ((c,d)::xs)
                   else assert_total $ maxIndex x ((a,b)::xs)

    gaussStepSwap : Fin (S $ minimum m n) -> DecompLUP mat -> DecompLUP mat
    gaussStepSwap i (MkLUP lu p sw) =
      let ir = minWeakenLeft {n=S n} i
          ic = minWeakenRight {m=S m} i
          maxi = head $ fst (maxIndex ([0],0) $ drop (cast i) $ enumerate $
                           indexSetRange [EndBound (weaken ir)] 0 $ getColumn ic lu)
      in  if maxi == ir then MkLUP (gaussStep i lu) p sw
          else MkLUP (gaussStep i $ swapRows ir maxi lu) (appendSwap maxi ir p) (S sw)


--------------------------------------------------------------------------------
-- Matrix properties
--------------------------------------------------------------------------------


||| Calculate the determinant of a matrix given its LUP decomposition.
export
detWithLUP : Num a => (mat : Matrix' n a) -> DecompLUP mat -> a
detWithLUP mat lup =
  (if numSwaps lup `mod` 2 == 0 then 1 else -1)
    * product (diagonal lup.lu)

||| Calculate the determinant of a matrix.
export
det : FieldCmp a => Matrix' n a -> a
det {n} mat with (viewShape mat)
  det {n=0} mat | Shape [0,0] = 1
  det {n=1} mat | Shape [1,1] = mat!![0,0]
  det {n=2} mat | Shape [2,2] = let [a,b,c,d] = elements mat in a*d - b*c
  _ | Shape [n,n] = detWithLUP mat (decompLUP mat)


--------------------------------------------------------------------------------
-- Solving matrix equations
--------------------------------------------------------------------------------


solveLowerTri' : Field a => Matrix' n a -> Vector n a -> Vector n a
solveLowerTri' {n} mat b with (viewShape b)
  _ | Shape [n] = vector $ reverse $ construct $ reverse $ toVect b
  where
    construct : {i : _} -> Vect i a -> Vect i a
    construct [] = []
    construct {i=S i} (b :: bs) =
      let xs = construct bs
          i' = assert_total $ case natToFin i n of Just i' => i'
      in (b - sum (zipWith (*) xs (reverse $ toVect $ believe_me $
                  mat !!.. [One i', EndBound (weaken i')]))) / mat!#[i,i] :: xs


solveUpperTri' : Field a => Matrix' n a -> Vector n a -> Vector n a
solveUpperTri' {n} mat b with (viewShape b)
  _ | Shape [n] = vector $ construct Z $ toVect b
  where
    construct : Nat -> Vect i a -> Vect i a
    construct _ [] = []
    construct i (b :: bs) =
      let xs = construct (S i) bs
          i' = assert_total $ case natToFin i n of Just i' => i'
      in (b - sum (zipWith (*) xs (toVect $ believe_me $
                  mat !!.. [One i', StartBound (FS i')]))) / mat!#[i,i] :: xs


||| Solve a linear equation, assuming the matrix is lower triangular.
||| Any entries other than those below the diagonal are ignored.
export
solveLowerTri : Field a => Matrix' n a -> Vector n a -> Maybe (Vector n a)
solveLowerTri mat b = if all (/=0) (diagonal mat)
                      then Just $ solveLowerTri' mat b
                      else Nothing

||| Solve a linear equation, assuming the matrix is upper triangular.
||| Any entries other than those above the diagonal are ignored.
export
solveUpperTri : Field a => Matrix' n a -> Vector n a -> Maybe (Vector n a)
solveUpperTri mat b = if all (/=0) (diagonal mat)
                      then Just $ solveUpperTri' mat b
                      else Nothing


solveWithLUP' : Field a => (mat : Matrix' n a) -> DecompLUP mat ->
                Vector n a -> Vector n a
solveWithLUP' mat lup b =
  let b' = permuteCoords (inverse lup.permute) b
  in solveUpperTri' lup.upper' $ solveLowerTri' lup.lower' b'

||| Solve a linear equation, given a matrix and its LUP decomposition.
export
solveWithLUP : Field a => (mat : Matrix' n a) -> DecompLUP mat ->
                Vector n a -> Maybe (Vector n a)
solveWithLUP mat lup b =
  let b' = permuteCoords (inverse lup.permute) b
  in solveUpperTri lup.upper' $ solveLowerTri' lup.lower' b'

||| Solve a linear equation given a matrix.
export
solve : FieldCmp a => Matrix' n a -> Vector n a -> Maybe (Vector n a)
solve mat = solveWithLUP mat (decompLUP mat)


--------------------------------------------------------------------------------
-- Matrix inversion
--------------------------------------------------------------------------------


||| Try to invert a square matrix, returning `Nothing` if an inverse
||| does not exist.
export
tryInverse : FieldCmp a => Matrix' n a -> Maybe (Matrix' n a)
tryInverse {n} mat with (viewShape mat)
  _ | Shape [n,n] =
    let lup = decompLUP mat
    in map hstack $ traverse (solveWithLUP mat lup) $ map basis range


export
{n : _} -> FieldCmp a => MultGroup (Matrix' n a) where
  inverse mat = let lup = decompLUP mat in
        hstack $ map (solveWithLUP' mat lup . basis) range

