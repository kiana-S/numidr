module Data.NumIdr.Vector

import Data.Vect
import Data.NumIdr.Multiply
import public Data.NumIdr.Array

%default total


||| A vector is a rank-1 array.
public export
Vector : Nat -> Type -> Type
Vector n = Array [n]


||| The length (number of dimensions) of the vector
public export
dim : Vector n a -> Nat
dim = head . shape

export
dimEq : (v : Vector n a) -> n = dim v
dimEq v = cong head $ shapeEq v


--------------------------------------------------------------------------------
-- Vector constructors
--------------------------------------------------------------------------------


||| Construct a vector from a `Vect`.
export
vector : Vect n a -> Vector n a
vector v = rewrite sym (lengthCorrect v)
           in fromVect [length v] $          -- the order doesn't matter here, as
           rewrite lengthCorrect v in        -- there is only 1 axis
           rewrite multOneLeftNeutral n in v

||| Convert a vector into a `Vect`.
export
toVect : Vector n a -> Vect n a
toVect v = believe_me $ Vect.fromList $ toList v


||| Return the `i`-th basis vector.
export
basis : Num a => {n : _} -> (i : Fin n) -> Vector n a
basis i = fromFunction _ (\[j] => if i == j then 1 else 0)


||| Calculate the 2D unit vector with the given angle off the x-axis.
export
unit2D : (ang : Double) -> Vector 2 Double
unit2D ang = vector [cos ang, sin ang]

||| Calculate the 3D unit vector corresponding to the given spherical coordinates,
||| where the polar axis is the z-axis.
|||
||| @ pol The polar angle of the vector
||| @ az  The azimuthal angle of the vector
export
unit3D : (pol, az : Double) -> Vector 3 Double
unit3D pol az = vector [cos az * sin pol, sin az * sin pol, cos pol]



--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

infixl 10 !!
infixl 10 !?

||| Index the vector at the given coordinate.
export
index : Fin n -> Vector n a -> a
index n = Array.index [n]

||| Index the vector at the given coordinate.
|||
||| This is the operator form of `index`.
export
(!!) : Vector n a -> Fin n -> a
(!!) = flip index

||| Index the vector at the given coordinate, returning `Nothing` if the
||| coordinate is out of bounds.
export
indexNB : Nat -> Vector n a -> Maybe a
indexNB n = Array.indexNB [n]

||| Index the vector at the given coordinate, returning `Nothing` if the
||| coordinate is out of bounds.
|||
||| This is the operator form of `indexNB`.
export
(!?) : Vector n a -> Nat -> Maybe a
(!?) = flip indexNB


-- Named projections

||| Return the x-coordinate (the first value) of the vector.
export
(.x) : Vector (1 + n) a -> a
(.x) = index FZ

||| Return the y-coordinate (the second value) of the vector.
export
(.y) : Vector (2 + n) a -> a
(.y) = index (FS FZ)

||| Return the z-coordinate (the third value) of the vector.
export
(.z) : Vector (3 + n) a -> a
(.z) = index (FS (FS FZ))


--------------------------------------------------------------------------------
-- Swizzling
--------------------------------------------------------------------------------


export
swizzle : Vect n (Fin m) -> Vector m a -> Vector n a
swizzle p v = rewrite sym (lengthCorrect p)
              in fromFunction [length p] (\[i] =>
                index (index (rewrite sym (lengthCorrect p) in i) p) v
              )



--------------------------------------------------------------------------------
-- Vector operations
--------------------------------------------------------------------------------


||| Concatenate one vector with another.
export
(++) : Vector m a -> Vector n a -> Vector (m + n) a
(++) = concat 0


||| Calculate the dot product of the two vectors.
export
dot : Num a => Vector n a -> Vector n a -> a
dot = sum .: zipWith (*)


||| Calculate the perpendicular product of the two vectors.
export
perp : Neg a => Vector 2 a -> Vector 2 a -> a
perp a b = a.x * b.y - a.y * b.x


