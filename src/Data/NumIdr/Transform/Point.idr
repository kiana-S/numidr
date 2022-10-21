module Data.NumIdr.Transform.Point

import Data.Vect
import Data.NumIdr.PrimArray
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Matrix
import Data.NumIdr.Interfaces

%default total


||| A point is a wrapper around the basic vector type, intended to be used with
||| `Transform`. These contain the exact same information as a vector, but
||| behave differently when transforms are applied to them.
export
record Point n a where
  constructor MkPoint
  vec : Vector n a

%name Point p,q,r


--------------------------------------------------------------------------------
-- Point constructors
--------------------------------------------------------------------------------


||| Construct a point from a vector.
export
fromVector : Vector n a -> Point n a
fromVector = MkPoint

||| Convert a point to a vector.
export
toVector : Point n a -> Vector n a
toVector = vec

||| Construct a point given its coordinates.
export
point : Vect n a -> Point n a
point = fromVector . vector


||| The origin point.
export
origin : Num a => {n : Nat} -> Point n a
origin = fromVector $ zeros [n]


--------------------------------------------------------------------------------
-- Point indexing
--------------------------------------------------------------------------------


infixl 10 !!
infixl 10 !?

||| Index the point at the given coordinate.
export
index : Fin n -> Point n a -> a
index i (MkPoint v) = index i v

||| Index the point at the given coordinate.
|||
||| This is the operator form of `index`.
export
(!!) : Point n a -> Fin n -> a
(!!) = flip index

||| Index the point at the given coordinate, returning `Nothing` if the index
||| is out of bounds.
export
indexNB : Nat -> Point n a -> Maybe a
indexNB n (MkPoint v) = indexNB n v

||| Index the point at the given coordinate, returning `Nothing` if the index
||| is out of bounds.
|||
||| This is the operator form of `indexNB`.
export
(!?) : Point n a -> Nat -> Maybe a
(!?) = flip indexNB


||| Return a `Vect` of the coordinates in the point.
export
toVect : Point n a -> Vect n a
toVect = toVect . vec


-- Named projections

||| Return the x-coordinate (the first value) of the vector.
export
(.x) : Point (1 + n) a -> a
(.x) = index FZ

||| Return the y-coordinate (the second value) of the vector.
export
(.y) : Point (2 + n) a -> a
(.y) = index (FS FZ)

||| Return the z-coordinate (the third value) of the vector.
export
(.z) : Point (3 + n) a -> a
(.z) = index (FS (FS FZ))


--------------------------------------------------------------------------------
-- Arithmetic operations
--------------------------------------------------------------------------------

infixr 8 +.
infixl 8 .+
infixl 8 -.

-- Affine space operations
-- These would have been named simply (+) and (-), but that caused
-- too many issues with interface resolution.

||| Add a vector to a point.
export
(+.) : Num a => Vector n a -> Point n a -> Point n a
a +. MkPoint b = MkPoint (zipWith (+) a b)

||| Add a point to a vector.
export
(.+) : Num a => Point n a -> Vector n a -> Point n a
MkPoint a .+ b = MkPoint (zipWith (+) a b)


||| Subtract two points to get the vector between them.
export
(-.) : Neg a => Point n a -> Point n a -> Vector n a
MkPoint a -. MkPoint b = zipWith (-) a b


--------------------------------------------------------------------------------
-- Interface implementations
--------------------------------------------------------------------------------


export
Zippable (Point n) where
  zipWith f (MkPoint v1) (MkPoint v2) = MkPoint (zipWith f v1 v2)
  zipWith3 f (MkPoint v1) (MkPoint v2) (MkPoint v3) = MkPoint (zipWith3 f v1 v2 v3)
  unzipWith f (MkPoint v) = bimap MkPoint MkPoint (unzipWith f v)
  unzipWith3 f (MkPoint v) = bimap MkPoint (bimap MkPoint MkPoint) (unzipWith3 f v)

export
Functor (Point n) where
  map f (MkPoint v) = MkPoint (map f v)

export
{n : _} -> Applicative (Point n) where
  pure = MkPoint . pure
  MkPoint f <*> MkPoint v = MkPoint (f <*> v)

{n : _} -> Monad (Point n) where
  join (MkPoint v) = MkPoint $ join $ map unwrap v
    where
      unwrap : Point n a -> Vector n a
      unwrap (MkPoint x) = x

export
Foldable (Point n) where
  foldl f z (MkPoint v) = foldl f z v
  foldr f z (MkPoint v) = foldr f z v
  null (MkPoint v) = null v
  toList (MkPoint v) = toList v

export
Traversable (Point n) where
  traverse f (MkPoint v) = map MkPoint (traverse f v)

export
Show a => Show (Point n a) where
  showPrec d (MkPoint v) = showCon d "point" $
    showArg $ PrimArray.toList $ getPrim v

export
Cast a b => Cast (Point n a) (Point n b) where
  cast (MkPoint v) = MkPoint (cast v)

export
Num a => Mult (Matrix m n a) (Point n a) (Point m a) where
  mat *. MkPoint v = MkPoint (mat *. v)
