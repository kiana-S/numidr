module Data.NumIdr.Array.Array

import Data.List
import Data.List1
import Data.Vect
import Data.Zippable
import Data.NumIdr.Multiply
import Data.NumIdr.PrimArray
import Data.NumIdr.Array.Order
import Data.NumIdr.Array.Coords

%default total

infix 2 !!
infix 2 !?
infixl 3 !!..
infix 3 !?..

||| Arrays are the central data structure of NumIdr. They are an `n`-dimensional
||| grid of values, where `n` is a value known as the *rank* of the array. Arrays
||| of rank 0 are single values, arrays of rank 1 are vectors, and arrays of rank
||| 2 are matrices.
|||
||| Each array has a *shape*, which is a vector of values giving the dimensions
||| of each axis of the array. The shape is also sometimes used to determine the
||| array's total size.
|||
||| Arrays are indexed by row first, as in the standard mathematical notation for
||| matrices. This is independent of the actual order in which they are stored; the
||| default order is row-major, but this is configurable.
|||
||| @ rk The rank of the array
||| @ s The shape of the array
||| @ a The type of the array's elements
export
data Array : (s : Vect rk Nat) -> (a : Type) -> Type where
  ||| Internally, arrays are stored using Idris's primitive array type. This is
  ||| stored along with the array's shape, and a vector of values called the
  ||| *strides*, which determine how indexes into the internal array should be
  ||| performed. This is how the order of the array is configurable.
  |||
  ||| @ ord The order of the elements of the array
  ||| @ sts The strides of the array
  ||| @ s   The shape of the array
  MkArray : (ord : Order) -> (sts : Vect rk Nat) ->
            (s : Vect rk Nat) -> PrimArray a -> Array s a


--------------------------------------------------------------------------------
-- Properties of arrays
--------------------------------------------------------------------------------


||| Extract the primitive array value.
export
getPrim : Array s a -> PrimArray a
getPrim (MkArray _ _ _ arr) = arr

||| The order of the elements of the array
export
getOrder : Array s a -> Order
getOrder (MkArray ord _ _ _) = ord

||| The strides of the array, returned in the same axis order as in the shape.
export
strides : Array {rk} s a -> Vect rk Nat
strides (MkArray _ sts _ _) = sts

||| The total number of elements of the array
||| This is equivalent to `product s`.
export
size : Array s a -> Nat
size = length . getPrim

||| The shape of the array
export
shape : Array {rk} s a -> Vect rk Nat
shape (MkArray _ _ s _) = s

||| The rank of the array
export
rank : Array s a -> Nat
rank = length . shape


-- Get a list of all coordinates
getAllCoords' : Vect rk Nat -> List (Vect rk Nat)
getAllCoords' = traverse (\case Z => []; S n => [0..n])

getAllCoords : (s : Vect rk Nat) -> List (Coords s)
getAllCoords [] = pure []
getAllCoords (Z :: s) = []
getAllCoords (S d :: s) = [| forget (allFins d) :: getAllCoords s |]


--------------------------------------------------------------------------------
-- Shape view
--------------------------------------------------------------------------------


export
shapeEq : (arr : Array s a) -> s = shape arr
shapeEq (MkArray _ _ _ _) = Refl


public export
data ShapeView : Array s a -> Type where
  Shape : (s : Vect rk Nat) -> {0 arr : Array s a} -> ShapeView arr

export
viewShape : (arr : Array s a) -> ShapeView arr
viewShape arr = rewrite shapeEq arr in
                  Shape (shape arr)
                  {arr = rewrite sym (shapeEq arr) in arr}


--------------------------------------------------------------------------------
-- Array constructors
--------------------------------------------------------------------------------


||| Create an array by repeating a single value.
|||
||| @ s    The shape of the constructed array
||| @ ord  The order of the constructed array
export
repeat' : (s : Vect rk Nat) -> (ord : Order) -> a -> Array s a
repeat' s ord x = MkArray ord (calcStrides ord s) s (constant (product s) x)

||| Create an array by repeating a single value.
||| To specify the order of the array, use `repeat'`.
|||
||| @ s The shape of the constructed array
export
repeat : (s : Vect rk Nat) -> a -> Array s a
repeat s = repeat' s COrder


export
zeros : Num a => (s : Vect rk Nat) -> Array s a
zeros s = repeat s 0

export
ones : Num a => (s : Vect rk Nat) -> Array s a
ones s = repeat s 1

||| Create an array given a vector of its elements. The elements of the vector
||| are arranged into the provided shape using the provided order.
|||
||| @ s   The shape of the constructed array
||| @ ord The order to interpret the elements
export
fromVect' : (s : Vect rk Nat) -> (ord : Order) -> Vect (product s) a -> Array s a
fromVect' s ord v = MkArray ord (calcStrides ord s) s (fromList $ toList v)

||| Create an array given a vector of its elements. The elements of the vector
||| are arranged into the provided shape using row-major order (the last axis is the
||| least significant).
||| To specify the order of the array, use `fromVect'`.
|||
||| @ s The shape of the constructed array
export
fromVect : (s : Vect rk Nat) -> Vect (product s) a -> Array s a
fromVect s = fromVect' s COrder

||| Create an array by taking values from a stream.
|||
||| @ s   The shape of the constructed array
||| @ ord The order to interpret the elements
export
fromStream' : (s : Vect rk Nat) -> (ord : Order) -> Stream a -> Array s a
fromStream' s ord st = MkArray ord (calcStrides ord s) s (fromList $ take (product s) st)

||| Create an array by taking values from a stream.
||| To specify the order of the array, use `fromStream'`.
|||
||| @ s The shape of the constructed array
export
fromStream : (s : Vect rk Nat) -> Stream a -> Array s a
fromStream s = fromStream' s COrder

||| Create an array given a function to generate its elements.
|||
||| @ s   The shape of the constructed array
||| @ ord The order to interpret the elements
export
fromFunction' : (s : Vect rk Nat) -> (ord : Order) -> (Coords s -> a) -> Array s a
fromFunction' s ord f = let sts = calcStrides ord s
                        in  MkArray ord sts s (unsafeFromIns (product s) $
                                     map (\is => (getLocation sts is, f is)) $ getAllCoords s)

||| Create an array given a function to generate its elements.
||| To specify the order of the array, use `fromFunction'`.
|||
||| @ s The shape of the constructed array
export
fromFunction : (s : Vect rk Nat) -> (Coords s -> a) -> Array s a
fromFunction s = fromFunction' s COrder

||| Construct an array using a structure of nested vectors. The elements are arranged
||| to the specified order before being written.
|||
||| @ s   The shape of the constructed array
||| @ ord The order of the constructed array
export
array' : (s : Vect rk Nat) -> (ord : Order) -> Vects s a -> Array s a
array' s ord v = MkArray ord sts s (unsafeFromIns (product s) ins)
  where
    sts : Vect rk Nat
    sts = calcStrides ord s

    ins : List (Nat, a)
    ins = collapse $ mapWithIndex (MkPair . getLocation' sts) v

||| Construct an array using a structure of nested vectors.
||| To explicitly specify the shape and order of the array, use `array'`.
export
array : {s : Vect rk Nat} -> Vects s a -> Array s a
array v = MkArray COrder (calcStrides COrder s) s (fromList $ collapse v)


--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------


||| Index the array using the given `Coords` object.
export
index : Coords s -> Array s a -> a
index is arr = index (getLocation (strides arr) is) (getPrim arr)

export
(!!) : Array s a -> Coords s -> a
(!!) = flip index

-- TODO: Create set/update at index functions

export
indexUpdate : Coords s -> (a -> a) -> Array s a -> Array s a
indexUpdate is f (MkArray ord sts s arr) = MkArray ord sts s (updateAt (getLocation sts is) f arr)

export
indexSet : Coords s -> a -> Array s a -> Array s a
indexSet is = indexUpdate is . const


export
indexNB : Vect rk Nat -> Array {rk} s a -> Maybe a
indexNB is arr with (viewShape arr)
  _ | Shape s = if concat @{All} $ zipWith (<) s (shape arr)
                then Just $ index (getLocation' (strides arr) is) (getPrim arr)
                else Nothing

export
(!?) : Array {rk} s a -> Vect rk Nat -> Maybe a
(!?) = flip indexNB

export
indexUpdateNB : Vect rk Nat -> (a -> a) -> Array {rk} s a -> Array s a
indexUpdateNB is f (MkArray ord sts s arr) = MkArray ord sts s (updateAt (getLocation' sts is) f arr)

export
indexSetNB : Vect rk Nat -> a -> Array {rk} s a -> Array s a
indexSetNB is = indexUpdateNB is . const


||| Index the array using the given `CoordsRange` object.
export
indexRange : (rs : CoordsRange s) -> Array s a -> Array (newShape rs) a
indexRange rs arr with (viewShape arr)
  _ | Shape s =
    let ord = getOrder arr
        sts = calcStrides ord s'
    in  MkArray ord sts s'
          (unsafeFromIns (product s') $
            map (\(is,is') => (getLocation' sts is',
                                index (getLocation' (strides arr) is) (getPrim arr)))
            $ getCoordsList rs)
  where s' : Vect ? Nat
        s' = newShape rs

export
(!!..) : Array s a -> (rs : CoordsRange s) -> Array (newShape rs) a
arr !!.. rs = indexRange rs arr


--------------------------------------------------------------------------------
-- Operations on arrays
--------------------------------------------------------------------------------


||| Reshape the array into the given shape and reinterpret it according to
||| the given order.
|||
||| @ s'  The shape to convert the array to
||| @ ord The order to reinterpret the array by
export
reshape' : (s' : Vect rk' Nat) -> (ord : Order) -> Array {rk} s a ->
             product s = product s' => Array s' a
reshape' s' ord' arr = MkArray ord' (calcStrides ord' s') s' (getPrim arr)

||| Reshape the array into the given shape.
|||
||| @ s' The shape to convert the array to
export
reshape : (s' : Vect rk' Nat) -> Array {rk} s a ->
            product s = product s' => Array s' a
reshape s' arr = reshape' s' (getOrder arr) arr


||| Change the internal order of the array's elements.
export
reorder : Order -> Array s a -> Array s a
reorder ord' arr with (viewShape arr)
  _ | Shape s = let sts = calcStrides ord' s
                in  MkArray ord' sts _ (unsafeFromIns (product s) $
                      map (\is => (getLocation' sts is, index (getLocation' (strides arr) is) (getPrim arr))) $
                      getAllCoords' s)


export
resize : (s' : Vect rk Nat) -> a -> Array {rk} s a -> Array s' a
resize s' x arr = fromFunction' s' (getOrder arr) (fromMaybe x . (arr !?) . toNB)

export
enumerate' : Array {rk} s a -> List (Vect rk Nat, a)
enumerate' (MkArray _ sts sh p) =
  map (\is => (is, index (getLocation' sts is) p)) (getAllCoords' sh)


export
enumerate : Array {rk} s a -> List (Coords s, a)
enumerate arr with (viewShape arr)
  _ | Shape s = map (\is => (is, index is arr)) (getAllCoords s)

export
concat : (axis : Fin rk) -> Array {rk} s a -> Array (replaceAt axis d s) a ->
        Array (updateAt axis (+d) s) a
concat axis a b = let sA = shape a
                      sB = shape b
                      dA = index axis sA
                      dB = index axis sB
                      s = replaceAt axis (dA + dB) sA
                      sts = calcStrides COrder s
                      ins = map (mapFst $ getLocation' sts . toNB) (enumerate a)
                            ++ map (mapFst $ getLocation' sts . updateAt axis (+dA) . toNB) (enumerate b)
                      -- TODO: prove that the type-level shape and `s` are equivalent
                  in  believe_me $ MkArray COrder sts s (unsafeFromIns (product s) ins)

export
stack : {s : _} -> (axis : Fin (S rk)) -> Vect n (Array {rk} s a) -> Array (insertAt axis n s) a
stack axis arrs = rewrite sym (lengthCorrect arrs) in
  fromFunction _ (\is => case getAxisInd axis (rewrite sym (lengthCorrect arrs) in is) of
                           (i,is') => index is' (index i arrs))
  where
    getAxisInd : {0 rk : _} -> {s : _} -> (ax : Fin (S rk)) -> Coords (insertAt ax n s) -> (Fin n, Coords s)
    getAxisInd FZ (i :: is) = (i, is)
    getAxisInd {s=_::_} (FS ax) (i :: is) = mapSnd (i::) (getAxisInd ax is)


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------


-- Most of these implementations apply the operation pointwise. If there are
-- multiple arrays involved with different orders, then all of the arrays are
-- reordered to match one.


export
Zippable (Array s) where
  zipWith f a b with (viewShape a)
    _ | Shape s = MkArray (getOrder a) (strides a) s $
                    if getOrder a == getOrder b
                      then unsafeZipWith f (getPrim a) (getPrim b)
                      else unsafeZipWith f (getPrim a) (getPrim $ reorder (getOrder a) b)

  zipWith3 f a b c with (viewShape a)
    _ | Shape s = MkArray (getOrder a) (strides a) s $
                    if (getOrder a == getOrder b) && (getOrder b == getOrder c)
                        then unsafeZipWith3 f (getPrim a) (getPrim b) (getPrim c)
                        else unsafeZipWith3 f (getPrim a) (getPrim $ reorder (getOrder a) b)
                                                          (getPrim $ reorder (getOrder a) c)

  unzipWith f arr with (viewShape arr)
    _ | Shape s = case unzipWith f (getPrim arr) of
                    (a, b) => (MkArray (getOrder arr) (strides arr) s a,
                               MkArray (getOrder arr) (strides arr) s b)

  unzipWith3 f arr with (viewShape arr)
    _ | Shape s = case unzipWith3 f (getPrim arr) of
                    (a, b, c) => (MkArray (getOrder arr) (strides arr) s a,
                                  MkArray (getOrder arr) (strides arr) s b,
                                  MkArray (getOrder arr) (strides arr) s c)

export
Functor (Array s) where
  map f (MkArray ord sts s arr) = MkArray ord sts s (map f arr)

export
{s : _} -> Applicative (Array s) where
  pure = repeat s
  (<*>) = zipWith apply

export
{s : _} -> Monad (Array s) where
  join arr = fromFunction s (\is => index is $ index is arr)


-- Foldable and Traversable operate on the primitive array directly. This means
-- that their operation is dependent on the order of the array.

export
Foldable (Array s) where
  foldl f z = foldl f z . getPrim
  foldr f z = foldr f z . getPrim
  null arr = size arr == Z
  toList = toList . getPrim

export
Traversable (Array s) where
  traverse f (MkArray ord sts s arr) =
    map (MkArray ord sts s) (traverse f arr)


export
Cast a b => Cast (Array s a) (Array s b) where
  cast = map cast

export
Eq a => Eq (Array s a) where
  a == b = if getOrder a == getOrder b
              then unsafeEq (getPrim a) (getPrim b)
              else unsafeEq (getPrim a) (getPrim $ reorder (getOrder a) b)

export
Semigroup a => Semigroup (Array s a) where
  (<+>) = zipWith (<+>)

export
{s : _} -> Monoid a => Monoid (Array s a) where
  neutral = repeat s neutral

-- The shape must be known at runtime here due to `fromInteger`. If `fromInteger`
-- were moved into its own interface, this constraint could be removed.
export
{s : _} -> Num a => Num (Array s a) where
  (+) = zipWith (+)
  (*) = zipWith (*)

  fromInteger = repeat s . fromInteger

export
{s : _} -> Neg a => Neg (Array s a) where
  negate = map negate
  (-) = zipWith (-)

{s : _} -> Fractional a => Fractional (Array s a) where
  recip = map recip
  (/) = zipWith (/)


export
Num a => Mult a (Array {rk} s a) where
  Result = Array {rk} s a
  (*.) x = map (*x)

export
Num a => Mult (Array {rk} s a) a where
  Result = Array {rk} s a
  (*.) = flip (*.)



export
Show a => Show (Array s a) where
  showPrec d arr = let orderedElems = PrimArray.toList $ getPrim $
                         if getOrder arr == COrder then arr else reorder COrder arr
                   in  showCon d "array " $ concat $ insertPunct (shape arr) $ map show orderedElems
    where
      splitWindow : Nat -> List String -> List (List String)
      splitWindow n xs = case splitAt n xs of
                           (xs, []) => [xs]
                           (l1, l2) => l1 :: splitWindow n (assert_smaller xs l2)

      insertPunct : Vect rk Nat -> List String -> List String
      insertPunct [] strs = strs
      insertPunct [d] strs = "[" :: intersperse ", " strs `snoc` "]"
      insertPunct (Z :: s) strs = ["[","]"]
      insertPunct (d :: s) strs =
        let secs = if null strs
                      then List.replicate d ("[]" :: Prelude.Nil)
                      else map (insertPunct s) $ splitWindow (length strs `div` d) strs
        in  "[" :: (concat $ intersperse [", "] secs) `snoc` "]"


--------------------------------------------------------------------------------
-- Numeric array operations
--------------------------------------------------------------------------------


export
lerp : Neg a => a -> Array s a -> Array s a -> Array s a
lerp t a b = zipWith (+) (a *. (1 - t)) (b *. t)


export
normSq : Num a => Array s a -> a
normSq arr = sum $ zipWith (*) arr arr

export
norm : Array s Double -> Double
norm = sqrt . normSq

export
normalize : Array s Double -> Array s Double
normalize arr = if all (==0) arr then arr else map (/ norm arr) arr

export
pnorm : (p : Double) -> Array s Double -> Double
pnorm p = (`pow` recip p) . sum . map (`pow` p)
