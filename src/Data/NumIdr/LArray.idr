module Data.NumIdr.LArray

import Data.Vect
import Data.NumIdr.PrimArray
import Data.NumIdr.Array

%default total


export
data LArray : Vect rk Nat -> Type -> Type where
  MkLArray : (ord : Order) -> (sts : Vect rk Nat) ->
             (s : Vect rk Nat) -> PrimArray a -> LArray s a

thaw : Array s a -> LArray s a
thaw {s} arr with (viewShape arr)
  _ | Shape s = MkLArray (getOrder arr) (strides arr) s (getPrim arr)

export
freeze : (1 _ : LArray s a) -> Array s a
freeze (MkLArray ord sts s arr) = unsafeMkArray ord sts s arr


--------------------------------------------------------------------------------
-- Constructor
--------------------------------------------------------------------------------


export
repeatL : (s : Vect rk Nat) -> a -> ((1 _ : LArray s a) -> LArray s' b) -> Array s' b
repeatL s x f = freeze $ f (thaw $ repeat s x)


export
zerosL : Num a => (s : Vect rk Nat) -> ((1 _ : LArray s a) -> LArray s' b) -> Array s' b
zerosL s f = freeze $ f (thaw $ zeros s)

export
onesL : Num a => (s : Vect rk Nat) -> ((1 _ : LArray s a) -> LArray s' b) -> Array s' b
onesL s f = freeze $ f (thaw $ ones s)


export
fromVectL : (s : Vect rk Nat) -> Vect (product s) a -> ((1 _ : LArray s a) -> LArray s' b) -> Array s' b
fromVectL s v f = freeze $ f (thaw $ fromVect s v)

export
fromStreamL : (s : Vect rk Nat) -> Stream a -> ((1 _ : LArray s a) -> LArray s' b) -> Array s' b
fromStreamL s xs f = freeze $ f (thaw $ fromStream s xs)

export
copyToL : Array s a -> ((1 _ : LArray s a) -> LArray s' b) -> Array s' b
copyToL {s} arr f with (viewShape arr)
  _ | Shape s =
    let ord = getOrder arr
        sts = strides arr
        prim = copy $ getPrim arr
    in  freeze $ f (thaw $ unsafeMkArray ord sts s prim)


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
index : Coords s -> (1 _ : LArray s a) -> Res a (const $ LArray s a)
index is (MkLArray ord sts s arr) =
  index (getLocation sts is) arr
    # MkLArray ord sts s arr

||| Index the array using the given coordinates.
|||
||| This is the operator form of `index`.
export %inline
(!!) : (1 _ : LArray s a) -> Coords s -> Res a (const $ LArray s a)
arr !! is = index is arr

||| Update the entry at the given coordinates using the function.
export
indexUpdate : Coords s -> (a -> a) -> (1 _ : LArray s a) -> LArray s a
indexUpdate is f (MkLArray ord sts s arr) =
  MkLArray ord sts s (unsafeUpdateInPlace (getLocation sts is) f arr)

||| Set the entry at the given coordinates to the given value.
export
indexSet : Coords s -> a -> (1 _ : LArray s a) -> LArray s a
indexSet is = indexUpdate is . const


||| Index the array using the given coordinates, returning `Nothing` if the
||| coordinates are out of bounds.
export
indexNB : Vect rk Nat -> (1 _ : LArray {rk} s a) -> Res (Maybe a) (const $ LArray s a)
indexNB is (MkLArray ord sts s arr) =
  (if all id $ zipWith (<) is s
    then Just $ index (getLocation' sts is) arr
    else Nothing)
    # MkLArray ord sts s arr

||| Index the array using the given coordinates, returning `Nothing` if the
||| coordinates are out of bounds.
|||
||| This is the operator form of `indexNB`.
export %inline
(!?) : (1 _ : LArray {rk} s a) -> Vect rk Nat -> Res (Maybe a) (const $ LArray s a)
arr !? is = indexNB is arr

||| Update the entry at the given coordinates using the function. `Nothing` is
||| returned if the coordinates are out of bounds.
export
indexUpdateNB : Vect rk Nat -> (a -> a) -> LArray {rk} s a -> Maybe (LArray s a)
indexUpdateNB is f (MkLArray ord sts s arr) =
  if all id $ zipWith (<) is s
  then Just $ MkLArray ord sts s (unsafeUpdateInPlace (getLocation' sts is) f arr)
  else Nothing

||| Set the entry at the given coordinates using the function. `Nothing` is
||| returned if the coordinates are out of bounds.
export
indexSetNB : Vect rk Nat -> a -> LArray {rk} s a -> Maybe (LArray s a)
indexSetNB is = indexUpdateNB is . const

||| Index the array using the given coordinates.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
export
indexUnsafe : Vect rk Nat -> (1 _ : LArray {rk} s a) -> Res a (const $ LArray s a)
indexUnsafe is (MkLArray ord sts s arr) =
  index (getLocation' sts is) arr
    # MkLArray ord sts s arr

||| Index the array using the given coordinates.
||| WARNING: This function does not perform any bounds check on its inputs.
||| Misuse of this function can easily break memory safety.
|||
||| This is the operator form of `indexUnsafe`.
export %inline
(!#) : (1 _ : LArray {rk} s a) -> Vect rk Nat -> Res a (const $ LArray s a)
arr !# is = indexUnsafe is arr
