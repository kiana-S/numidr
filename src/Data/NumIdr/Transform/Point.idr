module Data.NumIdr.Transform.Point

import Data.Vect
import Data.NumIdr.PrimArray
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Matrix
import Data.NumIdr.Interfaces

%default total


export
record Point n a where
  constructor MkPoint
  vec : Vector n a

%name Point p,q,r


--------------------------------------------------------------------------------
-- Point constructors
--------------------------------------------------------------------------------


export
fromVector : Vector n a -> Point n a
fromVector = MkPoint

export
toVector : Point n a -> Vector n a
toVector = vec

export
point : Vect n a -> Point n a
point = fromVector . vector


export
origin : Num a => {n : Nat} -> Point n a
origin = fromVector $ zeros [n]


--------------------------------------------------------------------------------
-- Point indexing
--------------------------------------------------------------------------------


infixl 10 !!
infixl 10 !?

export
index : Fin n -> Point n a -> a
index n (MkPoint v) = index n v

export
(!!) : Point n a -> Fin n -> a
(!!) = flip index

export
indexNB : Nat -> Point n a -> Maybe a
indexNB n (MkPoint v) = indexNB n v

export
(!?) : Point n a -> Nat -> Maybe a
(!?) = flip indexNB


export
toVect : Point n a -> Vect n a
toVect = toVect . vec


-- Named projections

export
(.x) : Point (1 + n) a -> a
(.x) = index FZ

export
(.y) : Point (2 + n) a -> a
(.y) = index (FS FZ)

export
(.z) : Point (3 + n) a -> a
(.z) = index (FS (FS FZ))


--------------------------------------------------------------------------------
-- Arithmetic operations
--------------------------------------------------------------------------------


-- Affine space operations
-- These seem to cause issues with interface resolution

-- namespace Left
--   export
--   (+) : Num a => Vector n a -> Point n a -> Point n a
--   a + MkPoint b = MkPoint (zipWith (+) a b)

-- namespace Right
--   export
--   (+) : Num a => Point n a -> Vector n a -> Point n a
--   MkPoint a + b = MkPoint (zipWith (+) a b)


-- export
-- (-) : Neg a => Point n a -> Point n a -> Vector n a
-- MkPoint a - MkPoint b = zipWith (-) a b


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
  showPrec d (MkPoint v) = showCon d "point " $
    show $ PrimArray.toList $ getPrim v

export
Cast a b => Cast (Point n a) (Point n b) where
  cast (MkPoint v) = MkPoint (cast v)

export
Num a => Mult (Matrix m n a) (Point n a) (Point m a) where
  mat *. MkPoint v = MkPoint (mat *. v)
