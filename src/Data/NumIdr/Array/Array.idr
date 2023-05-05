module Data.NumIdr.Array.Array

import Data.List
import Data.Vect
import Data.Zippable
import Data.NP
import Data.Permutation
import Data.NumIdr.Interfaces
import Data.NumIdr.PrimArray
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords

%default total


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
  MkArray : (rep : Rep) -> (rc : RepConstraint rep a) => (s : Vect rk Nat) ->
               PrimArray rep s a @{rc} -> Array s a

%name Array arr


export
unsafeMkArray : (rep : Rep) -> (rc : RepConstraint rep a) => (s : Vect rk Nat) ->
                  PrimArray rep s a @{rc} -> Array s a
unsafeMkArray = MkArray


--------------------------------------------------------------------------------
-- Properties of arrays
--------------------------------------------------------------------------------


||| The shape of the array
export
shape : Array {rk} s a -> Vect rk Nat
shape (MkArray _ s _) = s

||| The rank of the array
export
rank : Array s a -> Nat
rank = length . shape

export
getRep : Array s a -> Rep
getRep (MkArray rep _ _) = rep

getRepC : (arr : Array s a) -> RepConstraint (getRep arr) a
getRepC (MkArray _ @{rc} _ _) = rc

export
getPrim : (arr : Array s a) -> PrimArray (getRep arr) s a @{getRepC arr}
getPrim (MkArray _ _ pr) = pr


--------------------------------------------------------------------------------
-- Shape view
--------------------------------------------------------------------------------

export
shapeEq : (arr : Array s a) -> s = shape arr
shapeEq (MkArray _ _ _) = Refl


||| A view for extracting the shape of an array.
public export
data ShapeView : Array s a -> Type where
  Shape : (s : Vect rk Nat) -> {0 arr : Array s a} -> ShapeView arr

||| The covering function for the view `ShapeView`. This function takes an array
||| of type `Array s a` and returns `Shape s`.
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
||| @ rep  The internal representation of the constructed array
export
repeat : {default B rep : Rep} -> RepConstraint rep a =>
            (s : Vect rk Nat) -> a -> Array s a
repeat s x = MkArray rep s (constant s x)

||| Create an array filled with zeros.
|||
||| @ s The shape of the constructed array
||| @ rep  The internal representation of the constructed array
export
zeros : {default B rep : Rep} -> RepConstraint rep a =>
            Num a => (s : Vect rk Nat) -> Array s a
zeros {rep} s = repeat {rep} s 0

||| Create an array filled with ones.
|||
||| @ s The shape of the constructed array
||| @ rep  The internal representation of the constructed array
export
ones : {default B rep : Rep} -> RepConstraint rep a =>
            Num a => (s : Vect rk Nat) -> Array s a
ones {rep} s = repeat {rep} s 1

||| Create an array given a vector of its elements. The elements of the vector
||| are arranged into the provided shape using the provided order.
|||
||| @ s   The shape of the constructed array
||| @ rep  The internal representation of the constructed array
export
fromVect : {default B rep : Rep} -> RepConstraint rep a =>
              (s : Vect rk Nat) -> Vect (product s) a -> Array s a
fromVect s v = ?fv


||| Create an array by taking values from a stream.
|||
||| @ s   The shape of the constructed array
||| @ rep  The internal representation of the constructed array
export
fromStream : {default B rep : Rep} -> RepConstraint rep a =>
                (s : Vect rk Nat) -> Stream a -> Array s a
fromStream {rep} s str = fromVect {rep} s (take _ str)

||| Create an array given a function to generate its elements.
|||
||| @ s   The shape of the constructed array
||| @ rep  The internal representation of the constructed array
export
fromFunctionNB : {default B rep : Rep} -> RepConstraint rep a =>
                    (s : Vect rk Nat) -> (Vect rk Nat -> a) -> Array s a
fromFunctionNB s f = MkArray rep s (PrimArray.fromFunctionNB s f)

||| Create an array given a function to generate its elements.
|||
||| @ s   The shape of the constructed array
||| @ rep  The internal representation of the constructed array
export
fromFunction : {default B rep : Rep} -> RepConstraint rep a =>
                  (s : Vect rk Nat) -> (Coords s -> a) -> Array s a
fromFunction s f = MkArray rep s (PrimArray.fromFunction s f)

||| Construct an array using a structure of nested vectors. The elements are arranged
||| to the specified order before being written.
|||
||| @ s   The shape of the constructed array
||| @ ord The order of the constructed array
export
array' : {default B rep : Rep} -> RepConstraint rep a =>
          (s : Vect rk Nat) -> Vects s a -> Array s a
array' s v = MkArray rep s (fromVects s v)

||| Construct an array using a structure of nested vectors.
||| To explicitly specify the shape and order of the array, use `array'`.
export
array : {default B rep : Rep} -> RepConstraint rep a =>
          {s : Vect rk Nat} -> Vects s a -> Array s a
array {rep} = array' {rep} _


--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

infixl 10 !!
infixl 10 !?
infixl 10 !#
infixl 11 !!..
infixl 11 !?..
infixl 11 !#..


||| Index the array using the given coordinates.
export
index : Coords s -> Array s a -> a
index is (MkArray _ _ arr) = PrimArray.index is arr

||| Index the array using the given coordinates.
|||
||| This is the operator form of `index`.
export %inline
(!!) : Array s a -> Coords s -> a
arr !! is = index is arr
{-
||| Update the entry at the given coordinates using the function.
export
indexUpdate : Coords s -> (a -> a) -> Array s a -> Array s a
indexUpdate is f (MkArray ord sts s arr) =
  MkArray ord sts s (updateAt (getLocation sts is) f arr)

||| Set the entry at the given coordinates to the given value.
export
indexSet : Coords s -> a -> Array s a -> Array s a
indexSet is = indexUpdate is . const


||| Index the array using the given range of coordinates, returning a new array.
export
indexRange : (rs : CoordsRange s) -> Array s a -> Array (newShape rs) a
indexRange {s} rs arr with (viewShape arr)
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

||| Index the array using the given range of coordinates, returning a new array.
|||
||| This is the operator form of `indexRange`.
export %inline
(!!..) : Array s a -> (rs : CoordsRange s) -> Array (newShape rs) a
arr !!.. rs = indexRange rs arr

||| Set the sub-array at the given range of coordinates to the given array.
export
indexSetRange : (rs : CoordsRange s) -> Array (newShape rs) a ->
                  Array s a -> Array s a
indexSetRange rs rpl (MkArray ord sts s arr) =
  MkArray ord sts s (unsafePerformIO $ do
    let arr' = copy arr
    unsafeDoIns (map (\(is,is') =>
      (getLocation' sts is, index (getLocation' (strides rpl) is') (getPrim rpl)))
        $ getCoordsList rs) arr'
    pure arr')


||| Update the sub-array at the given range of coordinates by applying
||| a function to it.
export
indexUpdateRange : (rs : CoordsRange s) ->
                    (Array (newShape rs) a -> Array (newShape rs) a) ->
                    Array s a -> Array s a
indexUpdateRange rs f arr = indexSetRange rs (f $ arr !!.. rs) arr
-}

||| Index the array using the given coordinates, returning `Nothing` if the
||| coordinates are out of bounds.
export
indexNB : Vect rk Nat -> Array {rk} s a -> Maybe a
indexNB is (MkArray _ _ arr) = PrimArray.indexNB is arr

||| Index the array using the given coordinates, returning `Nothing` if the
||| coordinates are out of bounds.
|||
||| This is the operator form of `indexNB`.
export %inline
(!?) : Array {rk} s a -> Vect rk Nat -> Maybe a
arr !? is = indexNB is arr
{-
||| Update the entry at the given coordinates using the function. `Nothing` is
||| returned if the coordinates are out of bounds.
export
indexUpdateNB : Vect rk Nat -> (a -> a) -> Array {rk} s a -> Maybe (Array s a)
indexUpdateNB is f (MkArray ord sts s arr) =
  if all id $ zipWith (<) is s
  then Just $ MkArray ord sts s (updateAt (getLocation' sts is) f arr)
  else Nothing

||| Set the entry at the given coordinates using the function. `Nothing` is
||| returned if the coordinates are out of bounds.
export
indexSetNB : Vect rk Nat -> a -> Array {rk} s a -> Maybe (Array s a)
indexSetNB is = indexUpdateNB is . const


||| Index the array using the given range of coordinates, returning a new array.
||| If any of the given indices are out of bounds, then `Nothing` is returned.
export
indexRangeNB : (rs : Vect rk CRangeNB) -> Array s a -> Maybe (Array (newShape s rs) a)
indexRangeNB {s} rs arr with (viewShape arr)
  _ | Shape s =
    if validateShape s rs
    then
      let ord = getOrder arr
          sts = calcStrides ord s'
      in  Just $ MkArray ord sts s'
            (unsafeFromIns (product s') $
              map (\(is,is') => (getLocation' sts is',
                                  index (getLocation' (strides arr) is) (getPrim arr)))
              $ getCoordsList s rs)
    else Nothing
  where s' : Vect ? Nat
        s' = newShape s rs

||| Index the array using the given range of coordinates, returning a new array.
||| If any of the given indices are out of bounds, then `Nothing` is returned.
|||
||| This is the operator form of `indexRangeNB`.
export %inline
(!?..) : Array s a -> (rs : Vect rk CRangeNB) -> Maybe (Array (newShape s rs) a)
arr !?.. rs = indexRangeNB rs arr
-}

||| Index the array using the given coordinates.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
export
indexUnsafe : Vect rk Nat -> Array {rk} s a -> a
indexUnsafe is (MkArray _ _ arr) = PrimArray.indexUnsafe is arr

||| Index the array using the given coordinates.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
|||
||| This is the operator form of `indexUnsafe`.
export %inline
(!#) : Array {rk} s a -> Vect rk Nat -> a
arr !# is = indexUnsafe is arr

{-
||| Index the array using the given range of coordinates, returning a new array.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
export
indexRangeUnsafe : (rs : Vect rk CRangeNB) -> Array s a -> Array (newShape s rs) a
indexRangeUnsafe {s} rs arr with (viewShape arr)
  _ | Shape s =
    let ord = getOrder arr
        sts = calcStrides ord s'
    in  MkArray ord sts s'
          (unsafeFromIns (product s') $
            map (\(is,is') => (getLocation' sts is',
                                index (getLocation' (strides arr) is) (getPrim arr)))
            $ getCoordsList s rs)
  where s' : Vect ? Nat
        s' = newShape s rs

||| Index the array using the given range of coordinates, returning a new array.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
|||
||| This is the operator form of `indexRangeUnsafe`.
export %inline
(!#..) : Array s a -> (rs : Vect rk CRangeNB) -> Array (newShape s rs) a
arr !#.. is = indexRangeUnsafe is arr



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
             (0 ok : product s = product s') => Array s' a
reshape' s' ord' arr = MkArray ord' (calcStrides ord' s') s' (getPrim arr)

||| Reshape the array into the given shape.
|||
||| @ s' The shape to convert the array to
export
reshape : (s' : Vect rk' Nat) -> Array {rk} s a ->
            (0 ok : product s = product s') => Array s' a
reshape s' arr = reshape' s' (getOrder arr) arr


||| Change the internal order of the array's elements.
export
reorder : Order -> Array s a -> Array s a
reorder {s} ord' arr with (viewShape arr)
  _ | Shape s = let sts = calcStrides ord' s
                in  MkArray ord' sts _ (unsafeFromIns (product s) $
                      map (\is => (getLocation' sts is, index (getLocation' (strides arr) is) (getPrim arr))) $
                      getAllCoords' s)


||| Resize the array to a new shape, preserving the coordinates of the original
||| elements. New coordinates are filled with a default value.
|||
||| @ s'  The shape to resize the array to
||| @ def The default value to fill the array with
export
resize : (s' : Vect rk Nat) -> (def : a) -> Array {rk} s a -> Array s' a
resize s' def arr = fromFunction' s' (getOrder arr) (fromMaybe def . (arr !?) . toNB)

||| Resize the array to a new shape, preserving the coordinates of the original
||| elements. This function requires a proof that the new shape is strictly
||| smaller than the current shape of the array.
|||
||| @ s' The shape to resize the array to
export
-- HACK: Come up with a solution that doesn't use `believe_me` or trip over some
-- weird bug in the type-checker
resizeLTE : (s' : Vect rk Nat) -> (0 ok : NP Prelude.id (zipWith LTE s' s)) =>
            Array {rk} s a -> Array s' a
resizeLTE s' arr = resize s' (believe_me ()) arr


||| List all of the values in an array in row-major order.
export
elements : Array {rk} s a -> Vect (product s) a
elements (MkArray _ sts sh p) =
  let elems = map (flip index p . getLocation' sts) (getAllCoords' sh)
  -- TODO: prove that the number of elements is `product s`
  in assert_total $ case toVect (product sh) elems of Just v => v


||| List all of the values in an array along with their coordinates.
export
enumerateNB : Array {rk} s a -> List (Vect rk Nat, a)
enumerateNB (MkArray _ sts sh p) =
  map (\is => (is, index (getLocation' sts is) p)) (getAllCoords' sh)

||| List all of the values in an array along with their coordinates.
export
enumerate : Array s a -> List (Coords s, a)
enumerate {s} arr with (viewShape arr)
  _ | Shape s = map (\is => (is, index is arr)) (getAllCoords s)


||| Join two arrays along a particular axis, e.g. combining two matrices
||| vertically or horizontally. All other axes of the arrays must have the
||| same dimensions.
|||
||| @ axis The axis to join the arrays on
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

||| Stack multiple arrays along a new axis, e.g. stacking vectors to form a matrix.
|||
||| @ axis The axis to stack the arrays along
export
stack : {s : _} -> (axis : Fin (S rk)) -> Vect n (Array {rk} s a) -> Array (insertAt axis n s) a
stack axis arrs = rewrite sym (lengthCorrect arrs) in
  fromFunction _ (\is => case getAxisInd axis (rewrite sym (lengthCorrect arrs) in is) of
                           (i,is') => index is' (index i arrs))
  where
    getAxisInd : {0 rk : _} -> {s : _} -> (ax : Fin (S rk)) -> Coords (insertAt ax n s) -> (Fin n, Coords s)
    getAxisInd FZ (i :: is) = (i, is)
    getAxisInd {s=_::_} (FS ax) (i :: is) = mapSnd (i::) (getAxisInd ax is)

export
joinAxes : {s' : _} -> Array s (Array s' a) -> Array (s ++ s') a
joinAxes {s} arr with (viewShape arr)
  _ | Shape s = fromFunctionNB (s ++ s') (\is => arr !# takeUpTo s is !# dropUpTo s is)
  where
    takeUpTo : Vect rk Nat -> Vect (rk + rk') Nat -> Vect rk Nat
    takeUpTo [] ys = []
    takeUpTo (x::xs) (y::ys) = y :: takeUpTo xs ys

    dropUpTo : Vect rk Nat -> Vect (rk + rk') Nat -> Vect rk' Nat
    dropUpTo [] ys = ys
    dropUpTo (x::xs) (y::ys) = dropUpTo xs ys


export
splitAxes : (rk : Nat) -> {0 rk' : Nat} -> {s : _} ->
            Array {rk=rk+rk'} s a -> Array (take {m=rk'} rk s) (Array (drop {m=rk'} rk s) a)
splitAxes _ {s} arr = fromFunctionNB _ (\is => fromFunctionNB _ (\is' => arr !# (is ++ is')))


||| Construct the transpose of an array by reversing the order of its axes.
export
transpose : Array s a -> Array (reverse s) a
transpose {s} arr with (viewShape arr)
  _ | Shape s = fromFunctionNB (reverse s) (\is => arr !# reverse is)

||| Construct the transpose of an array by reversing the order of its axes.
|||
||| This is the postfix form of `transpose`.
export
(.T) : Array s a -> Array (reverse s) a
(.T) = transpose


||| Swap two axes in an array.
export
swapAxes : (i,j : Fin rk) -> Array s a -> Array (swapElems i j s) a
swapAxes {s} i j arr with (viewShape arr)
  _ | Shape s = fromFunctionNB _ (\is => arr !# swapElems i j is)

||| Apply a permutation to the axes of an array.
export
permuteAxes : (p : Permutation rk) -> Array s a -> Array (permuteVect p s) a
permuteAxes {s} p arr with (viewShape arr)
  _ | Shape s = fromFunctionNB _ (\is => arr !# permuteVect p s)

||| Swap two coordinates along a specific axis (e.g. swapping two rows in a matrix).
|||
||| @ axis The axis to swap the coordinates along. Slices of the array
||| perpendicular to this axis are taken when swapping.
export
swapInAxis : (axis : Fin rk) -> (i,j : Fin (index axis s)) -> Array s a -> Array s a
swapInAxis {s} axis i j arr with (viewShape arr)
  _ | Shape s = fromFunctionNB _ (\is => arr !# updateAt axis (swapValues i j) is)

||| Permute the coordinates along a specific axis (e.g. permuting the rows in
||| a matrix).
|||
||| @ axis The axis to permute the coordinates along. Slices of the array
||| perpendicular to this axis are taken when permuting.
export
permuteInAxis : (axis : Fin rk) -> Permutation (index axis s) -> Array s a -> Array s a
permuteInAxis {s} axis p arr with (viewShape arr)
  _ | Shape s = fromFunctionNB _ (\is => arr !# updateAt axis (permuteValues p) is)


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------


-- Most of these implementations apply the operation pointwise. If there are
-- multiple arrays involved with different orders, then all of the arrays are
-- reordered to match one.


export
Zippable (Array s) where
  zipWith {s} f a b with (viewShape a)
    _ | Shape s = MkArray (getOrder a) (strides a) s $
                    if getOrder a == getOrder b
                      then unsafeZipWith f (getPrim a) (getPrim b)
                      else unsafeZipWith f (getPrim a) (getPrim $ reorder (getOrder a) b)

  zipWith3 {s} f a b c with (viewShape a)
    _ | Shape s = MkArray (getOrder a) (strides a) s $
                    if (getOrder a == getOrder b) && (getOrder b == getOrder c)
                        then unsafeZipWith3 f (getPrim a) (getPrim b) (getPrim c)
                        else unsafeZipWith3 f (getPrim a) (getPrim $ reorder (getOrder a) b)
                                                          (getPrim $ reorder (getOrder a) c)

  unzipWith {s} f arr with (viewShape arr)
    _ | Shape s = case unzipWith f (getPrim arr) of
                    (a, b) => (MkArray (getOrder arr) (strides arr) s a,
                               MkArray (getOrder arr) (strides arr) s b)

  unzipWith3 {s} f arr with (viewShape arr)
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
  join arr = fromFunction s (\is => arr !! is !! is)


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

export
{s : _} -> Fractional a => Fractional (Array s a) where
  recip = map recip
  (/) = zipWith (/)


export
Num a => Mult a (Array {rk} s a) (Array s a) where
  (*.) x = map (*x)

export
Num a => Mult (Array {rk} s a) a (Array s a) where
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


||| Linearly interpolate between two arrays.
export
lerp : Neg a => a -> Array s a -> Array s a -> Array s a
lerp t a b = zipWith (+) (a *. (1 - t)) (b *. t)


||| Calculate the square of an array's Eulidean norm.
export
normSq : Num a => Array s a -> a
normSq arr = sum $ zipWith (*) arr arr

||| Calculate an array's Eucliean norm.
export
norm : Array s Double -> Double
norm = sqrt . normSq

||| Normalize the array to a norm of 1.
|||
||| If the array contains all zeros, then it is returned unchanged.
export
normalize : Array s Double -> Array s Double
normalize arr = if all (==0) arr then arr else map (/ norm arr) arr

||| Calculate the Lp-norm of an array.
export
pnorm : (p : Double) -> Array s Double -> Double
pnorm p = (`pow` recip p) . sum . map (`pow` p)
-}
