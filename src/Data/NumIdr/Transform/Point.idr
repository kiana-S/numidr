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
-- Interface implementations
--------------------------------------------------------------------------------


namespace Right
  export
  (+) : Num a => Point n a -> Vector n a -> Point n a
  MkPoint a + b = MkPoint (zipWith (+) a b)

namespace Left
  export
  (+) : Num a => Vector n a -> Point n a -> Point n a
  a + MkPoint b = MkPoint (zipWith (+) a b)


export
(-) : Neg a => Point n a -> Point n a -> Vector n a
MkPoint a - MkPoint b = zipWith (-) a b


--------------------------------------------------------------------------------
-- Interface implementations
--------------------------------------------------------------------------------


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
