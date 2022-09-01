module Data.NumIdr.Matrix

import Data.List
import Data.Vect
import Data.Bool.Xor
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
public export
record DecompLU {0 n,a : _} (mat : Matrix' n a) where
  constructor MkLU
  lower, upper : Matrix' n a

export
Show a => Show (DecompLU {a} mat) where
  showPrec p (MkLU l u) = showCon p "MkLU" $ showArg l ++ showArg u


iterateN : (n : Nat) -> (Fin n -> a -> a) -> a -> a
iterateN 0 f x = x
iterateN 1 f x = f FZ x
iterateN (S n@(S _)) f x = iterateN n (f . FS) $ f FZ x

export
decompLU : Neg a => Fractional a => (mat : Matrix' n a) -> DecompLU mat
decompLU {n} mat with (viewShape mat)
  _ | Shape [n,n] = iterateN n doolittle (MkLU identity mat)
  where
    doolittle : Fin n -> DecompLU mat -> DecompLU mat
    doolittle i (MkLU l u) =
      let v = rewrite rangeLen (S i') n in fromFunctionNB [minus n (S i')]
                (\[x] => u!#[S i' + x,i'] / u!#[i',i'])
          low = indexSetRange [StartBound (FS i), One i] (-v) identity
      in MkLU (indexSetRange [StartBound (FS i), One i] v l) (low *. u)
      where i' : Nat
            i' = cast i


-- LUP Decomposition
public export
record DecompLUP {0 n,a : _} (mat : Matrix' n a) where
  constructor MkLUP
  lower, upper, permute : Matrix' n a
  swaps : Nat

export
Show a => Show (DecompLUP {a} mat) where
  showPrec p (MkLUP l u pr b) = showCon p "MkLUP" $
    showArg l ++ showArg u ++ showArg pr ++ showArg b

export
fromLU : Num a => DecompLU {n,a} mat -> DecompLUP mat
fromLU {n} (MkLU l u) with (viewShape l)
  _ | Shape [n,n] = MkLUP l u identity 0

export
decompLUP : Ord a => Abs a => Neg a => Fractional a =>
            (mat : Matrix' n a) -> DecompLUP mat
decompLUP {n} mat with (viewShape mat)
  decompLUP {n=0} mat | Shape [0,0] = MkLUP mat mat mat 0
  decompLUP {n=S n} mat | Shape [S n,S n] =
    iterateN (S n) doolittle (MkLUP identity mat identity 0)
  where
    maxIndex : (s,a) -> List (s,a) -> (s,a)
    maxIndex x [] = x
    maxIndex _ [x] = x
    maxIndex x ((a,b)::(c,d)::xs) =
      if abs b < abs d then assert_total $ maxIndex x ((c,d)::xs)
                       else assert_total $ maxIndex x ((a,b)::xs)

    doolittle : Fin (S n) -> DecompLUP mat -> DecompLUP mat
    doolittle i (MkLUP l u p sw) =
      let (maxi, maxv) = mapFst ((+i') . head)
                           (maxIndex ([0],0) $ enumerateNB $
                           u !!.. [StartBound (weaken i), One i])
          u' = if maxi == i' then u
               else fromFunctionNB _ (\[x,y] =>
                 if x==i' then u!#[maxi,y]
                 else if x==maxi then u!#[i',y]
                 else u!#[x,y])
          p' = if maxi == i' then p
               else fromFunctionNB _ (\[x,y] =>
                 if x==i' then p!#[maxi,y]
                 else if x==maxi then p!#[i',y]
                 else p!#[x,y])
          v = rewrite rangeLen (S i') (S n) in fromFunctionNB [minus n i']
                (\[x] => u'!#[S i' + x,i'] / u'!#[i',i'])
          low = indexSetRange [StartBound (FS i), One i] (-v) identity
      in if maxv == 0 then MkLUP l u p sw else
            MkLUP (indexSetRange [StartBound (FS i), One i] v l)
              (low *. u') p' (if maxi==i' then S sw else sw)
      where i' : Nat
            i' = cast i


--------------------------------------------------------------------------------
-- Matrix properties
--------------------------------------------------------------------------------


export
det : Ord a => Abs a => Neg a => Fractional a =>
      Matrix' n a -> a
det {n} mat with (viewShape mat)
  det {n=0} mat | Shape [0,0] = 1
  det {n=1} mat | Shape [1,1] = mat!![0,0]
  det {n=2} mat | Shape [2,2] = let [a,b,c,d] = elements mat in a*d - b*c
  _ | Shape [n,n] = let MkLUP l u p sw = decompLUP mat
                    in (if sw `mod` 2 == 0 then 1 else -1)
                          * product (diagonal l) * product (diagonal u)
