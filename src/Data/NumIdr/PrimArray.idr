module Data.NumIdr.PrimArray

import Data.Buffer
import Data.Vect
import Data.NP
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords
import Data.NumIdr.PrimArray.Bytes
import Data.NumIdr.PrimArray.Boxed
import Data.NumIdr.PrimArray.Linked
import Data.NumIdr.PrimArray.Delayed

%default total


public export
RepConstraint : Rep -> Type -> Type
RepConstraint (Bytes _) a = ByteRep a
RepConstraint (Boxed _) a = ()
RepConstraint Linked a = ()
RepConstraint Delayed a = ()


export
PrimArray : (rep : Rep) -> Vect rk Nat -> (a : Type) -> RepConstraint rep a => Type
PrimArray (Bytes o) s a = PrimArrayBytes o s
PrimArray (Boxed o) s a = PrimArrayBoxed o s a
PrimArray Linked s a = Vects s a
PrimArray Delayed s a = Coords s -> a


export
constant : {rep : Rep} -> RepConstraint rep a => (s : Vect rk Nat) -> a -> PrimArray rep s a
constant {rep = Bytes o} = Bytes.constant
constant {rep = Boxed o} = Boxed.constant
constant {rep = Linked} = Linked.constant
constant {rep = Delayed} = Delayed.constant

export
fromFunctionNB : {rep : Rep} -> RepConstraint rep a => (s : Vect rk Nat) -> (Vect rk Nat -> a) -> PrimArray rep s a
fromFunctionNB {rep = Bytes o} @{rc} s f =
  let sts = calcStrides o s
  in  Bytes.unsafeFromIns @{rc} s ((\is => (getLocation' sts is, f is)) <$> getAllCoords' s)
fromFunctionNB {rep = Boxed o} s f =
  let sts = calcStrides o s
  in  Boxed.unsafeFromIns s ((\is => (getLocation' sts is, f is)) <$> getAllCoords' s)
fromFunctionNB {rep = Linked} s f = Linked.fromFunctionNB f
fromFunctionNB {rep = Delayed} s f = f . toNB

export
fromFunction : {rep : Rep} -> RepConstraint rep a => (s : Vect rk Nat) -> (Coords s -> a) -> PrimArray rep s a
fromFunction {rep = Bytes o} @{rc} s f =
  let sts = calcStrides o s
  in  Bytes.unsafeFromIns @{rc} s ((\is => (getLocation sts is, f is)) <$> getAllCoords s)
fromFunction {rep = Boxed o} s f =
  let sts = calcStrides o s
  in  Boxed.unsafeFromIns s ((\is => (getLocation sts is, f is)) <$> getAllCoords s)
fromFunction {rep = Linked} s f = Linked.fromFunction f
fromFunction {rep = Delayed} s f = f

export
index : {rep,s : _} -> RepConstraint rep a => Coords s -> PrimArray rep s a -> a
index {rep = Bytes o} is arr@(MkPABytes sts _) = index (getLocation sts is) arr
index {rep = Boxed o} is arr@(MkPABoxed sts _) = index (getLocation sts is) arr
index {rep = Linked} is arr = Linked.index is arr
index {rep = Delayed} is arr = arr is

export
indexNB : {rep,s : _} -> RepConstraint rep a => Vect rk Nat -> PrimArray {rk} rep s a -> Maybe a
indexNB {rep = Bytes o} is arr@(MkPABytes sts _) =
  if and (zipWith (delay .: (<)) is s)
  then Just $ index (getLocation' sts is) arr
  else Nothing
indexNB {rep = Boxed o} is arr@(MkPABoxed sts _) =
  if and (zipWith (delay .: (<)) is s)
  then Just $ index (getLocation' sts is) arr
  else Nothing
indexNB {rep = Linked} is arr = (`Linked.index` arr) <$> checkRange s is
indexNB {rep = Delayed} is arr = arr <$> checkRange s is

export
indexUnsafe : {rep,s : _} -> RepConstraint rep a => Vect rk Nat -> PrimArray {rk} rep s a -> a
indexUnsafe {rep = Bytes o} is arr@(MkPABytes sts _) = index (getLocation' sts is) arr
indexUnsafe {rep = Boxed o} is arr@(MkPABoxed sts _) = index (getLocation' sts is) arr
indexUnsafe {rep = Linked} is arr = assert_total $ case checkRange s is of
  Just is' => Linked.index is' arr
indexUnsafe {rep = Delayed} is arr = assert_total $ case checkRange s is of
  Just is' => arr is'

export
convertRep : {r1,r2,s : _} -> RepConstraint r1 a => RepConstraint r2 a => PrimArray r1 s a -> PrimArray r2 s a
convertRep {r1 = Bytes o, r2 = Bytes o'} @{rc} arr = reorder @{rc} arr
convertRep {r1 = Boxed o, r2 = Boxed o'} arr = reorder arr
convertRep {r1 = Linked, r2 = Linked} arr = arr
convertRep {r1 = Linked, r2 = Bytes COrder} @{_} @{rc} arr = fromList @{rc} s (collapse arr)
convertRep {r1 = Linked, r2 = Boxed COrder} arr = fromList s (collapse arr)
convertRep {r1 = Delayed, r2 = Delayed} arr = arr
convertRep {r1, r2} arr = fromFunction s (\is => PrimArray.index is arr)

export
fromVects : {rep : Rep} -> RepConstraint rep a => (s : Vect rk Nat) -> Vects s a -> PrimArray rep s a
fromVects s v = convertRep {r1=Linked} v
