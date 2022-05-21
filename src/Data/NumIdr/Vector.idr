module Data.NumIdr.Vector

import Data.Vect
import public Data.NumIdr.Array

%default total

public export
Vector : Nat -> Type -> Type
Vector n = Array [n]


--------------------------------------------------------------------------------
-- Vector constructors
--------------------------------------------------------------------------------


export
vector : Vect n a -> Vector n a
vector v = rewrite sym (lengthCorrect v)
           in fromVect [length v] $          -- the order doesn't matter here, as
           rewrite lengthCorrect v in        -- there is only 1 axis
           rewrite multOneLeftNeutral n in v

export
basis : Num a => {n : _} -> (i : Fin n) -> Vector n a
basis i = fromFunction _ (\[j] => if i == j then 1 else 0)


export
unit2D : (ang : Double) -> Vector 2 Double
unit2D ang = vector [cos ang, sin ang]

export
unit3D : (pol, az : Double) -> Vector 3 Double
unit3D pol az = vector [cos az * sin pol, sin az * sin pol, cos pol]



--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------


export
index : Fin n -> Vector n a -> a
index n = Array.index [n]


-- Named projections
export
(.x) : Vector (1 + n) a -> a
(.x) = index FZ

export
(.y) : Vector (2 + n) a -> a
(.y) = index (FS FZ)

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


export
dot : Num a => Vector n a -> Vector n a -> a
dot = sum .: zipWith (*)


export
perp : Neg a => Vector 2 a -> Vector 2 a -> a
perp a b = a.x * b.y - a.y * b.x

