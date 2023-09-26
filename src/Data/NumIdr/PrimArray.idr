module Data.NumIdr.PrimArray

import Data.Buffer
import Data.Vect
import Data.Fin
import Data.NP
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords
import public Data.NumIdr.PrimArray.Bytes
import public Data.NumIdr.PrimArray.Boxed
import public Data.NumIdr.PrimArray.Linked
import public Data.NumIdr.PrimArray.Delayed

%default total



noRCCorrect : (rep : Rep) -> NoConstraintRep rep -> RepConstraint rep a
noRCCorrect (Boxed _) BoxedNC = ()
noRCCorrect Linked LinkedNC = ()
noRCCorrect Delayed DelayedNC = ()

export
mergeRepConstraint : {r, r' : Rep} -> RepConstraint r a -> RepConstraint r' a ->
                      RepConstraint (mergeRep r r') a
mergeRepConstraint {r,r'} a b with (r == Delayed || r' == Delayed)
  _ | True = ()
  _ | False = a

export
mergeNCRepConstraint : {r, r' : Rep} -> RepConstraint (mergeRepNC r r') a
mergeNCRepConstraint = noRCCorrect _ (mergeRepNCCorrect r r')

export
forceRepConstraint : {r : Rep} -> RepConstraint (forceRepNC r) a
forceRepConstraint = noRCCorrect _ (forceRepNCCorrect r)



export
PrimArray : (rep : Rep) -> Vect rk Nat -> (a : Type) -> RepConstraint rep a => Type
PrimArray (Bytes o) s a = PrimArrayBytes o s
PrimArray (Boxed o) s a = PrimArrayBoxed o s a
PrimArray Linked s a = Vects s a
PrimArray Delayed s a = Coords s -> a


export
reshape : {rep : Rep} -> LinearRep rep => RepConstraint rep a => (s' : Vect rk Nat) -> PrimArray rep s a -> PrimArray rep s' a
reshape {rep = Bytes o} s' (MkPABytes _ arr) = MkPABytes (calcStrides o s') arr
reshape {rep = Boxed o} s' (MkPABoxed _ arr) = MkPABoxed (calcStrides o s') arr

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
indexUpdate : {rep,s : _} -> RepConstraint rep a => Coords s -> (a -> a) -> PrimArray rep s a -> PrimArray rep s a
indexUpdate {rep = Bytes o} @{rc} is f arr@(MkPABytes sts _) =
  let i = getLocation sts is
  in create @{rc} s (\n => let x = index n arr in if n == i then f x else x)
indexUpdate {rep = Boxed o} is f arr@(MkPABoxed sts _) =
  let i = getLocation sts is
  in create s (\n => let x = index n arr in if n == i then f x else x)
indexUpdate {rep = Linked} is f arr = update is f arr
indexUpdate {rep = Delayed} is f arr =
  \is' =>
    let x = arr is'
    in if eqNP is is' then f x else x

export
indexRange : {rep,s : _} -> RepConstraint rep a => (rs : CoordsRange s) -> PrimArray rep s a
              -> PrimArray rep (newShape rs) a
indexRange {rep = Bytes o} @{rc} rs arr@(MkPABytes sts _) =
  let s' : Vect ? Nat
      s' = newShape rs
      sts' := calcStrides o s'
  in unsafeFromIns @{rc} (newShape rs) $
        map (\(is,is') => (getLocation' sts' is',
                            index (getLocation' sts is) arr))
        $ getCoordsList rs
indexRange {rep = Boxed o} rs arr@(MkPABoxed sts _) =
  let s' : Vect ? Nat
      s' = newShape rs
      sts' := calcStrides o s'
  in unsafeFromIns (newShape rs) $
        map (\(is,is') => (getLocation' sts' is',
                            index (getLocation' sts is) arr))
        $ getCoordsList rs
indexRange {rep = Linked} rs arr = Linked.indexRange rs arr
indexRange {rep = Delayed} rs arr = Delayed.indexRange rs arr

export
indexSetRange : {rep,s : _} -> RepConstraint rep a => (rs : CoordsRange s)
              -> PrimArray rep (newShape rs) a -> PrimArray rep s a -> PrimArray rep s a
indexSetRange {rep = Bytes o} @{rc} rs rpl@(MkPABytes sts' _) arr@(MkPABytes sts _) =
  unsafePerformIO $ do
    let arr' = copy arr
    unsafeDoIns @{rc} (map (\(is,is') =>
      (getLocation' sts is, index (getLocation' sts' is') rpl))
        $ getCoordsList rs) arr'
    pure arr'
indexSetRange {rep = Boxed o} rs rpl@(MkPABoxed sts' _) arr@(MkPABoxed sts _) =
  unsafePerformIO $ do
    let arr' = copy arr
    unsafeDoIns (map (\(is,is') =>
      (getLocation' sts is, index (getLocation' sts' is') rpl))
        $ getCoordsList rs) arr'
    pure arr'
indexSetRange {rep = Linked} rs rpl arr = Linked.indexSetRange rs rpl arr
indexSetRange {rep = Delayed} rs rpl arr = Delayed.indexSetRange rs rpl arr

export
indexUnsafe : {rep,s : _} -> RepConstraint rep a => Vect rk Nat -> PrimArray {rk} rep s a -> a
indexUnsafe {rep = Bytes o} is arr@(MkPABytes sts _) = index (getLocation' sts is) arr
indexUnsafe {rep = Boxed o} is arr@(MkPABoxed sts _) = index (getLocation' sts is) arr
indexUnsafe {rep = Linked} is arr = assert_total $ case validateCoords s is of
  Just is' => Linked.index is' arr
indexUnsafe {rep = Delayed} is arr = assert_total $ case validateCoords s is of
  Just is' => arr is'

export
convertRepPrim : {r1,r2,s : _} -> RepConstraint r1 a => RepConstraint r2 a => PrimArray r1 s a -> PrimArray r2 s a
convertRepPrim {r1 = Bytes o, r2 = Bytes o'} @{rc} arr = reorder @{rc} arr
convertRepPrim {r1 = Boxed o, r2 = Boxed o'} arr = reorder arr
convertRepPrim {r1 = Linked, r2 = Linked} arr = arr
convertRepPrim {r1 = Linked, r2 = Bytes COrder} @{_} @{rc} arr = fromList @{rc} s (collapse arr)
convertRepPrim {r1 = Linked, r2 = Boxed COrder} arr = fromList s (collapse arr)
convertRepPrim {r1 = Delayed, r2 = Delayed} arr = arr
convertRepPrim {r1, r2} arr = fromFunction s (\is => PrimArray.index is arr)

export
fromVects : {rep : Rep} -> RepConstraint rep a => (s : Vect rk Nat) -> Vects s a -> PrimArray rep s a
fromVects s v = convertRepPrim {r1=Linked} v

export
fromList : {rep : Rep} -> LinearRep rep => RepConstraint rep a => (s : Vect rk Nat) -> List a -> PrimArray rep s a
fromList {rep = (Boxed x)} = Boxed.fromList
fromList {rep = (Bytes x)} = Bytes.fromList

export
mapPrim : {rep,s : _} -> RepConstraint rep a => RepConstraint rep b =>
        (a -> b) -> PrimArray rep s a -> PrimArray rep s b
mapPrim {rep = (Bytes x)} @{_} @{rc} f arr = Bytes.create @{rc} _ (\i => f $ Bytes.index i arr)
mapPrim {rep = (Boxed x)} f arr = Boxed.create _ (\i => f $ Boxed.index i arr)
mapPrim {rep = Linked} f arr = Linked.mapVects f arr
mapPrim {rep = Delayed} f arr = f . arr


export
foldl : {rep,s : _} -> RepConstraint rep a => (b -> a -> b) -> b -> PrimArray rep s a -> b
foldl {rep = Bytes _} = Bytes.foldl
foldl {rep = Boxed _} = Boxed.foldl
foldl {rep = Linked} = Linked.foldl
foldl {rep = Delayed} = \f,z => Boxed.foldl f z . convertRepPrim {r1=Delayed,r2=B}

export
foldr : {rep,s : _} -> RepConstraint rep a => (a -> b -> b) -> b -> PrimArray rep s a -> b
foldr {rep = Bytes _} = Bytes.foldr
foldr {rep = Boxed _} = Boxed.foldr
foldr {rep = Linked} = Linked.foldr
foldr {rep = Delayed} = \f,z => Boxed.foldr f z . convertRepPrim {r1=Delayed,r2=B}

export
traverse : {rep,s : _} -> Applicative f => RepConstraint rep a => RepConstraint rep b =>
            (a -> f b) -> PrimArray rep s a -> f (PrimArray rep s b)
traverse {rep = Bytes o} = Bytes.traverse
traverse {rep = Boxed o} = Boxed.traverse
traverse {rep = Linked} = Linked.traverse
traverse {rep = Delayed} = \f => map (convertRepPrim @{()} @{()} {r1=B,r2=Delayed}) .
                                  Boxed.traverse f .
                                  convertRepPrim @{()} @{()} {r1=Delayed,r2=B}
