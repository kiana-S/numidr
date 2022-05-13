module Data.NumIdr.Array.Array

import Data.Vect
import Data.NumIdr.PrimArray
import Data.NumIdr.Array.Order
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
  ||| @ s   The shape of the array
  ||| @ sts The strides of the array
  MkArray : (s : Vect rk Nat) -> (sts : Vect rk Nat) -> PrimArray a -> Array s a


||| Extract the primitive array value.
export
getPrim : Array s a -> PrimArray a
getPrim (MkArray _ _ arr) = arr

||| The strides of the array, returned in the same axis order as in the shape.
export
getStrides : Array {rk} s a -> Vect rk Nat
getStrides (MkArray _ sts _) = sts

||| The total number of elements of the array
||| This is equivalent to `product s`.
export
size : Array s a -> Nat
size = length . getPrim

||| The shape of the array
export
shape : Array {rk} s a -> Vect rk Nat
shape (MkArray s _ _) = s

||| The rank of the array
export
rank : Array s a -> Nat
rank = length . shape


||| Create an array given a vector of its elements. The elements of the vector
||| are arranged into the provided shape using the provided order.
|||
||| @ s   The shape of the constructed array
||| @ ord The order to interpret the elements
export
fromVect' : (s : Vect rk Nat) -> (ord : Order rk) -> Vect (product s) a -> Array s a
fromVect' s ord v = MkArray s (calcStrides ord s) (fromList $ toList v)

||| Create an array given a vector of its elements. The elements of the vector
||| are assembled into the provided shape using row-major order (the last axis is the
||| least significant).
|||
||| @ s The shape of the constructed array
export
fromVect : (s : Vect rk Nat) -> Vect (product s) a -> Array s a
fromVect s = fromVect' s COrder


||| Construct an array using a structure of nested vectors. The elements are arranged
||| to the specified order before being written.
|||
||| @ s   The shape of the constructed array
||| @ ord The order of the constructed array
export
array' : (s : Vect rk Nat) -> (ord : Order rk) -> Vects s a -> Array s a
array' s ord v = MkArray s sts (unsafeFromIns (product s) ins)
  where
    sts : Vect rk Nat
    sts = calcStrides ord s

    ins : List (Nat, a)
    ins = collapse $ mapWithIndex (\i,x => (sum $ zipWith (*) i sts, x)) v

||| Construct an array using a structure of nested vectors.
export
array : {s : _} -> Vects s a -> Array s a
array v = MkArray s (calcStrides COrder s) (fromList $ collapse v)


||| Reshape the array into the given shape and reinterpret it according to
||| the given order.
|||
||| @ s'  The shape to convert the array to
||| @ ord The order to reinterpret the array by
export
reshape' : (s' : Vect rk' Nat) -> (ord : Order rk') -> Array {rk} s a ->
             product s = product s' => Array s' a
reshape' s' ord' arr = MkArray s' (calcStrides ord' s') (getPrim arr)

||| Reshape the array into the given shape.
|||
||| The array is also reinterpreted in row-major order; if this is undesirable,
||| then `reshape'` must be used instead.
|||
||| @ s' The shape to convert the array to
export
reshape : (s' : Vect rk' Nat) -> Array {rk} s a ->
            product s = product s' => Array s' a
reshape s' = reshape' s' COrder


||| Index the array using the given `Coords` object.
export
index : Coords s -> Array s a -> a
index is arr = index (getLocation (getStrides arr) is) (getPrim arr)
