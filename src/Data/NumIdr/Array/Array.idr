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


||| The type of an array.
|||
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
||| matrices.
|||
||| @ rk The rank of the array
||| @ s The shape of the array
||| @ a The type of the array's elements
export
data Array : (s : Vect rk Nat) -> (a : Type) -> Type where
  ||| Internally, arrays are stored via one of a handful of representations.
  |||
  ||| @ s   The shape of the array
  ||| @ rep The internal representation of the array
  ||| @ rc  A witness that the element type satisfies the representation constraint
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


||| The shape of the array.
export
shape : Array {rk} s a -> Vect rk Nat
shape (MkArray _ s _) = s

||| The rank of the array.
export
rank : Array s a -> Nat
rank = length . shape

||| The internal representation of the array.
export
getRep : Array s a -> Rep
getRep (MkArray rep _ _) = rep

||| The representation constraint of the array.
export
getRepC : (arr : Array s a) -> RepConstraint (getRep arr) a
getRepC (MkArray _ @{rc} _ _) = rc

||| Extract the primitive backend array.
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
repeat s x = MkArray rep s (PrimArray.constant s x)

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
fromVect : {default B rep : Rep} -> LinearRep rep => RepConstraint rep a =>
              (s : Vect rk Nat) -> Vect (product s) a -> Array s a
fromVect {rep} s v = MkArray rep s (PrimArray.fromList {rep} s $ toList v)


||| Create an array by taking values from a stream.
|||
||| @ s   The shape of the constructed array
||| @ rep  The internal representation of the constructed array
export
fromStream : {default B rep : Rep} -> LinearRep rep => RepConstraint rep a =>
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

||| Update the entry at the given coordinates using the function.
export
indexUpdate : Coords s -> (a -> a) -> Array s a -> Array s a
indexUpdate is f (MkArray rep @{rc} s arr) =
  MkArray rep @{rc} s (indexUpdate @{rc} is f arr)

||| Set the entry at the given coordinates to the given value.
export
indexSet : Coords s -> a -> Array s a -> Array s a
indexSet is = indexUpdate is . const


||| Index the array using the given range of coordinates, returning a new array.
export
indexRange : (rs : CoordsRange s) -> Array s a -> Array (newShape rs) a
indexRange rs (MkArray rep @{rc} s arr) =
  MkArray rep @{rc} _ (PrimArray.indexRange @{rc} rs arr)

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
indexSetRange rs (MkArray _ _ rpl) (MkArray rep s arr) =
  MkArray rep s (PrimArray.indexSetRange {rep} rs (convertRepPrim rpl) arr)


||| Update the sub-array at the given range of coordinates by applying
||| a function to it.
export
indexUpdateRange : (rs : CoordsRange s) ->
                    (Array (newShape rs) a -> Array (newShape rs) a) ->
                    Array s a -> Array s a
indexUpdateRange rs f arr = indexSetRange rs (f $ arr !!.. rs) arr


||| Index the array using the given coordinates, returning `Nothing` if the
||| coordinates are out of bounds.
export
indexNB : Vect rk Nat -> Array {rk} s a -> Maybe a
indexNB is (MkArray rep @{rc} s arr) =
  map (\is => index is (MkArray rep @{rc} s arr)) (validateCoords s is)

||| Index the array using the given coordinates, returning `Nothing` if the
||| coordinates are out of bounds.
|||
||| This is the operator form of `indexNB`.
export %inline
(!?) : Array {rk} s a -> Vect rk Nat -> Maybe a
arr !? is = indexNB is arr

||| Update the entry at the given coordinates using the function. `Nothing` is
||| returned if the coordinates are out of bounds.
export
indexUpdateNB : Vect rk Nat -> (a -> a) -> Array {rk} s a -> Maybe (Array s a)
indexUpdateNB is f (MkArray rep @{rc} s arr) =
  map (\is => indexUpdate is f (MkArray rep @{rc} s arr)) (validateCoords s is)

||| Set the entry at the given coordinates using the function. `Nothing` is
||| returned if the coordinates are out of bounds.
export
indexSetNB : Vect rk Nat -> a -> Array {rk} s a -> Maybe (Array s a)
indexSetNB is = indexUpdateNB is . const


||| Index the array using the given range of coordinates, returning a new array.
||| If any of the given indices are out of bounds, then `Nothing` is returned.
export
indexRangeNB : (rs : Vect rk CRangeNB) -> Array s a -> Maybe (Array (newShape s rs) a)
indexRangeNB rs (MkArray rep @{rc} s arr) =
  map (\rs => believe_me $ Array.indexRange rs (MkArray rep @{rc} s arr)) (validateCRange s rs)

||| Index the array using the given range of coordinates, returning a new array.
||| If any of the given indices are out of bounds, then `Nothing` is returned.
|||
||| This is the operator form of `indexRangeNB`.
export %inline
(!?..) : Array s a -> (rs : Vect rk CRangeNB) -> Maybe (Array (newShape s rs) a)
arr !?.. rs = indexRangeNB rs arr


||| Index the array using the given coordinates.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
export %unsafe
indexUnsafe : Vect rk Nat -> Array {rk} s a -> a
indexUnsafe is (MkArray _ _ arr) = PrimArray.indexUnsafe is arr

||| Index the array using the given coordinates.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
|||
||| This is the operator form of `indexUnsafe`.
export %inline %unsafe
(!#) : Array {rk} s a -> Vect rk Nat -> a
arr !# is = indexUnsafe is arr


||| Index the array using the given range of coordinates, returning a new array.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
export %unsafe
indexRangeUnsafe : (rs : Vect rk CRangeNB) -> Array s a -> Array (newShape s rs) a
indexRangeUnsafe rs (MkArray rep @{rc} s arr) =
  believe_me $ Array.indexRange (assertCRange s rs) (MkArray rep @{rc} s arr)

||| Index the array using the given range of coordinates, returning a new array.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
|||
||| This is the operator form of `indexRangeUnsafe`.
export %inline %unsafe
(!#..) : Array s a -> (rs : Vect rk CRangeNB) -> Array (newShape s rs) a
arr !#.. is = indexRangeUnsafe is arr



--------------------------------------------------------------------------------
-- Operations on arrays
--------------------------------------------------------------------------------

||| Map a function over an array.
|||
||| You should almost always use `map` instead; only use this function if you
||| know what you are doing!
export
mapArray' : (a -> a) -> Array s a -> Array s a
mapArray' f (MkArray rep _ arr) = MkArray rep _ (mapPrim f arr)

||| Map a function over an array.
|||
||| You should almost always use `map` instead; only use this function if you
||| know what you are doing!
export
mapArray : (a -> b) -> (arr : Array s a) -> RepConstraint (getRep arr) b => Array s b
mapArray f (MkArray rep _ arr) @{rc} = MkArray rep @{rc} _ (mapPrim f arr)

||| Combine two arrays of the same element type using a binary function.
|||
||| You should almost always use `zipWith` instead; only use this function if
||| you know what you are doing!
export
zipWithArray' : (a -> a -> a) -> Array s a -> Array s a -> Array s a
zipWithArray' {s} f a b with (viewShape a)
  _ | Shape s = MkArray (mergeRep (getRep a) (getRep b))
                          @{mergeRepConstraint (getRepC a) (getRepC b)} s
                          $ PrimArray.fromFunctionNB @{mergeRepConstraint (getRepC a) (getRepC b)} _
                              (\is => f (a !# is) (b !# is))

||| Combine two arrays using a binary function.
|||
||| You should almost always use `zipWith` instead; only use this function if
||| you know what you are doing!
export
zipWithArray : (a -> b -> c) -> (arr : Array s a) -> (arr' : Array s b) ->
                RepConstraint (mergeRep (getRep arr) (getRep arr')) c => Array s c
zipWithArray {s} f a b @{rc} with (viewShape a)
  _ | Shape s = MkArray (mergeRep (getRep a) (getRep b)) @{rc} s
                          $ PrimArray.fromFunctionNB _ (\is => f (a !# is) (b !# is))


||| Reshape the array into the given shape.
|||
||| @ s' The shape to convert the array to
export
reshape : (s' : Vect rk' Nat) -> (arr : Array {rk} s a) -> LinearRep (getRep arr) =>
            (0 ok : product s = product s') => Array s' a
reshape s' (MkArray rep _ arr) = MkArray rep s' (PrimArray.reshape s' arr)

||| Change the internal representation of the array's elements.
export
convertRep : (rep : Rep) -> RepConstraint rep a => Array s a -> Array s a
convertRep rep (MkArray _ s arr) = MkArray rep s (convertRepPrim arr)

||| Resize the array to a new shape, preserving the coordinates of the original
||| elements. New coordinates are filled with a default value.
|||
||| @ s'  The shape to resize the array to
||| @ def The default value to fill the array with
export
resize : (s' : Vect rk Nat) -> (def : a) -> Array {rk} s a -> Array s' a
resize s' def arr = fromFunction {rep=getRep arr} @{getRepC arr} s' (fromMaybe def . (arr !?) . toNB)

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


||| List all of the values in an array along with their coordinates.
export
enumerateNB : Array {rk} s a -> List (Vect rk Nat, a)
enumerateNB (MkArray _ s arr) =
  map (\is => (is, PrimArray.indexUnsafe is arr)) (getAllCoords' s)

||| List all of the values in an array along with their coordinates.
export
enumerate : Array s a -> List (Coords s, a)
enumerate {s} arr with (viewShape arr)
  _ | Shape s = map (\is => (is, index is arr)) (getAllCoords s)

||| List all of the values in an array in row-major order.
export
elements : Array {rk} s a -> Vect (product s) a
elements (MkArray _ s arr) =
  believe_me $ Vect.fromList $
    map (flip PrimArray.indexUnsafe arr) (getAllCoords' s)

||| Join two arrays along a particular axis, e.g. combining two matrices
||| vertically or horizontally. All other axes of the arrays must have the
||| same dimensions.
|||
||| @ axis The axis to join the arrays on
export
concat : (axis : Fin rk) -> Array {rk} s a -> Array (replaceAt axis d s) a ->
          Array (updateAt axis (+d) s) a
concat {s,d} axis a b with (viewShape a, viewShape b)
  _ | (Shape s, Shape (replaceAt axis d s)) =
    believe_me $ Array.fromFunctionNB {rep=mergeRep (getRep a) (getRep b)}
                  @{mergeRepConstraint (getRepC a) (getRepC b)} (updateAt axis (+ index axis (shape b)) s)
      (\is => let limit = index axis s
              in if index axis is < limit then a !# is else b !# updateAt axis (`minus` limit) is)

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

||| Join the axes of a nested array structure to form a single array.
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


||| Split an array into a nested array structure along the specified axes.
export
splitAxes : (rk : Nat) -> {0 rk' : Nat} -> {s : _} ->
            Array {rk=rk+rk'} s a -> Array (take {m=rk'} rk s) (Array (drop {m=rk'} rk s) a)
splitAxes _ {s} arr = fromFunctionNB _ (\is => fromFunctionNB _ (\is' => arr !# (is ++ is')))

||| Construct the transpose of an array by reversing the order of its axes.
export
transpose : Array s a -> Array (reverse s) a
transpose {s} arr with (viewShape arr)
  _ | Shape s = fromFunctionNB _ (\is => arr !# reverse is)

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

export
Zippable (Array s) where
  zipWith {s} f a b with (viewShape a)
    _ | Shape s = MkArray (mergeRepNC (getRep a) (getRep b))
                          @{mergeNCRepConstraint} s
                          $ PrimArray.fromFunctionNB @{mergeNCRepConstraint} _
                              (\is => f (a !# is) (b !# is))

  zipWith3 {s} f a b c with (viewShape a)
    _ | Shape s = MkArray (mergeRepNC (mergeRep (getRep a) (getRep b)) (getRep c))
                          @{mergeNCRepConstraint} s
                          $ PrimArray.fromFunctionNB @{mergeNCRepConstraint} _
                              (\is => f (a !# is) (b !# is) (c !# is))

  unzipWith {s} f arr with (viewShape arr)
    _ | Shape s =
      let rep : Rep
          rep = forceRepNC $ getRep arr
      in  (MkArray rep
             @{forceRepConstraint} s
             $ PrimArray.fromFunctionNB @{forceRepConstraint} _
                 (\is => fst $ f (arr !# is)),
           MkArray rep
             @{forceRepConstraint} s
             $ PrimArray.fromFunctionNB @{forceRepConstraint} _
                 (\is => snd $ f (arr !# is)))

  unzipWith3 {s} f arr with (viewShape arr)
    _ | Shape s =
      let rep : Rep
          rep = forceRepNC $ getRep arr
      in  (MkArray rep
             @{forceRepConstraint} s
             $ PrimArray.fromFunctionNB @{forceRepConstraint} _
                 (\is => fst $ f (arr !# is)),
           MkArray rep
             @{forceRepConstraint} s
             $ PrimArray.fromFunctionNB @{forceRepConstraint} _
                 (\is => fst $ snd $ f (arr !# is)),
           MkArray rep
             @{forceRepConstraint} s
             $ PrimArray.fromFunctionNB @{forceRepConstraint} _
                 (\is => snd $ snd $ f (arr !# is)))


export
Functor (Array s) where
  map f (MkArray rep @{rc} s arr) = MkArray (forceRepNC rep) @{forceRepConstraint} s
                                (mapPrim @{forceRepConstraint} @{forceRepConstraint} f
                                  $ convertRepPrim @{rc} @{forceRepConstraint} arr)

export
{s : _} -> Applicative (Array s) where
  pure = repeat s
  (<*>) = zipWith apply

export
{s : _} -> Monad (Array s) where
  join arr = fromFunction s (\is => arr !! is !! is)


-- Foldable and Traversable operate on the primitive array directly. This means
-- that their operation is dependent on the internal representation of the
-- array.

export
Foldable (Array s) where
  foldl f z (MkArray _ _ arr) = PrimArray.foldl f z arr
  foldr f z (MkArray _ _ arr) = PrimArray.foldr f z arr
  null (MkArray _ s _) = isZero (product s)


export
Traversable (Array s) where
  traverse f (MkArray rep @{rc} s arr) =
    map (MkArray (forceRepNC rep) @{forceRepConstraint} s)
      (PrimArray.traverse {rep=forceRepNC rep}
        @{%search} @{forceRepConstraint} @{forceRepConstraint} f
        (convertRepPrim @{rc} @{forceRepConstraint} arr))


export
Cast a b => Cast (Array s a) (Array s b) where
  cast = map cast

export
Eq a => Eq (Array s a) where
  a == b = and $ zipWith (delay .: (==)) (convertRep D a) (convertRep D b)

export
Semigroup a => Semigroup (Array s a) where
  (<+>) = zipWithArray' (<+>)

export
{s : _} -> Monoid a => Monoid (Array s a) where
  neutral = repeat s neutral

-- The shape must be known at runtime here due to `fromInteger`. If `fromInteger`
-- were moved into its own interface, this constraint could be removed.
export
{s : _} -> Num a => Num (Array s a) where
  (+) = zipWithArray' (+)
  (*) = zipWithArray' (*)

  fromInteger = repeat s . fromInteger

export
{s : _} -> Neg a => Neg (Array s a) where
  negate = mapArray' negate
  (-) = zipWithArray' (-)

export
{s : _} -> Fractional a => Fractional (Array s a) where
  recip = mapArray' recip
  (/) = zipWithArray' (/)


export
Num a => Mult a (Array {rk} s a) (Array s a) where
  (*.) x = mapArray' (*x)

export
Num a => Mult (Array {rk} s a) a (Array s a) where
  (*.) = flip (*.)


export
Show a => Show (Array s a) where
  showPrec d arr = let orderedElems = toList $ elements arr
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
lerp t a b = zipWithArray' (+) (a *. (1 - t)) (b *. t)


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
