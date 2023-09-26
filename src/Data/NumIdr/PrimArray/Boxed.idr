module Data.NumIdr.PrimArray.Boxed

import Data.Buffer
import System
import Data.IORef
import Data.IOArray.Prims
import Data.Vect
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords
import Data.NumIdr.PrimArray.Bytes

%default total


public export
data PrimArrayBoxed : Order -> Vect rk Nat -> Type -> Type where
  MkPABoxed : (sts : Vect rk Nat) -> ArrayData a -> PrimArrayBoxed {rk} o s a


-- Private helper functions for ArrayData primitives
export
newArrayData : Nat -> a -> IO (ArrayData a)
newArrayData n x = fromPrim $ prim__newArray (cast n) x

export
arrayDataGet : Nat -> ArrayData a -> IO a
arrayDataGet n arr = fromPrim $ prim__arrayGet arr (cast n)

export
arrayDataSet : Nat -> a -> ArrayData a -> IO ()
arrayDataSet n x arr = fromPrim $ prim__arraySet arr (cast n) x


fromArray : {o : _} -> (s : Vect rk Nat) -> ArrayData a -> PrimArrayBoxed o s a
fromArray s = MkPABoxed (calcStrides o s)

arrayAction : {o : _} -> (s : Vect rk Nat) -> (ArrayData a -> IO ()) -> PrimArrayBoxed o s a
arrayAction s action = fromArray s $ unsafePerformIO $ do
  arr <- newArrayData (product s) (believe_me ())
  action arr
  pure arr

||| Construct an array with a constant value.
export
constant : {o : _} -> (s : Vect rk Nat) -> a -> PrimArrayBoxed o s a
constant s x = fromArray s $ unsafePerformIO $ newArrayData (product s) x


export
unsafeDoIns : List (Nat, a) -> PrimArrayBoxed o s a -> IO ()
unsafeDoIns ins (MkPABoxed _ arr) = for_ ins $ \(i,x) => arrayDataSet i x arr

||| Construct an array from a list of "instructions" to write a value to a
||| particular index.
export
unsafeFromIns : {o : _} -> (s : Vect rk Nat) -> List (Nat, a) -> PrimArrayBoxed o s a
unsafeFromIns s ins = arrayAction s $ \arr =>
    for_ ins $ \(i,x) => arrayDataSet i x arr

||| Create an array given its size and a function to generate its elements by
||| its index.
export
create : {o : _} -> (s : Vect rk Nat) -> (Nat -> a) -> PrimArrayBoxed o s a
create s f = arrayAction s $ \arr =>
    for_ [0..pred (product s)] $ \i => arrayDataSet i (f i) arr

||| Index into a primitive array. This function is unsafe, as it performs no
||| boundary check on the index given.
export
index : Nat -> PrimArrayBoxed o s a -> a
index n (MkPABoxed _ arr) = unsafePerformIO $ arrayDataGet n arr

export
copy : {o,s : _} -> PrimArrayBoxed o s a -> PrimArrayBoxed o s a
copy arr = create s (\n => index n arr)


export
reorder : {o,o',s : _} -> PrimArrayBoxed o s a -> PrimArrayBoxed o' s a
reorder arr@(MkPABoxed sts ar) =
  if o == o' then MkPABoxed sts ar
  else let sts' = calcStrides o' s
       in  unsafeFromIns s
            ((\is => (getLocation' sts' is, index (getLocation' sts is) arr))
              <$> getAllCoords' s)

export
bytesToBoxed : {s : _} -> ByteRep a => PrimArrayBytes o s -> PrimArrayBoxed o s a
bytesToBoxed (MkPABytes sts buf) = MkPABoxed sts $ unsafePerformIO $ do
  arr <- newArrayData (product s) (believe_me ())
  for_ [0..pred (product s)] $ \i => arrayDataSet i !(readBuffer i buf) arr
  pure arr

export
boxedToBytes : {s : _} -> ByteRep a => PrimArrayBoxed o s a -> PrimArrayBytes o s
boxedToBytes @{br} (MkPABoxed sts arr) = MkPABytes sts $ unsafePerformIO $ do
  Just buf <- newBuffer $ cast (product s * bytes @{br})
    | Nothing => die "Cannot create array"
  for_ [0..pred (product s)] $ \i => writeBuffer i !(arrayDataGet i arr) buf
  pure buf


export
fromList : {o : _} -> (s : Vect rk Nat) -> List a -> PrimArrayBoxed o s a
fromList s xs = arrayAction s $ go xs 0
  where
    go : List a -> Nat -> ArrayData a -> IO ()
    go [] _ buf = pure ()
    go (x :: xs) i buf = arrayDataSet i x buf >> go xs (S i) buf


export
foldl : {s : _} -> (b -> a -> b) -> b -> PrimArrayBoxed o s a -> b
foldl f z (MkPABoxed sts arr) =
  if product s == 0 then z
  else unsafePerformIO $ do
    ref <- newIORef z
    for_ [0..pred $ product s] $ \n => do
        x <- readIORef ref
        y <- arrayDataGet n arr
        writeIORef ref (f x y)
    readIORef ref

export
foldr : {s : _} -> (a -> b -> b) -> b -> PrimArrayBoxed o s a -> b
foldr f z (MkPABoxed sts arr) =
  if product s == 0 then z
  else unsafePerformIO $ do
    ref <- newIORef z
    for_ [pred $ product s..0] $ \n => do
         x <- arrayDataGet n arr
         y <- readIORef ref
         writeIORef ref (f x y)
    readIORef ref

export
traverse : {o,s : _} -> Applicative f => (a -> f b) -> PrimArrayBoxed o s a -> f (PrimArrayBoxed o s b)
traverse f = map (Boxed.fromList _) . traverse f . foldr (::) []

{-
export
updateAt : Nat -> (a -> a) -> PrimArrayBoxed o s a -> PrimArrayBoxed o s a
updateAt n f arr = if n >= length arr then arr else
  unsafePerformIO $ do
    let cpy = copy arr
    x <- arrayDataGet n cpy.content
    arrayDataSet n (f x) cpy.content
    pure cpy

export
unsafeUpdateInPlace : Nat -> (a -> a) -> PrimArrayBoxed a -> PrimArrayBoxed a
unsafeUpdateInPlace n f arr = unsafePerformIO $ do
  x <- arrayDataGet n arr.content
  arrayDataSet n (f x) arr.content
  pure arr

||| Convert a primitive array to a list.
export
toList : PrimArrayBoxed a -> List a
toList arr = iter (length arr) []
  where
    iter : Nat -> List a -> List a
    iter Z acc = acc
    iter (S n) acc = let el = index n arr
                     in  iter n (el :: acc)

||| Construct a primitive array from a list.
export
fromList : List a -> PrimArrayBoxed a
fromList xs = create (length xs)
    (\n => assert_total $ fromJust $ getAt n xs)
  where
    partial
    fromJust : Maybe a -> a
    fromJust (Just x) = x



export
unsafeZipWith : (a -> b -> c) -> PrimArrayBoxed a -> PrimArrayBoxed b -> PrimArrayBoxed c
unsafeZipWith f a b = create (length a) (\n => f (index n a) (index n b))

export
unsafeZipWith3 : (a -> b -> c -> d) ->
                 PrimArrayBoxed a -> PrimArrayBoxed b -> PrimArrayBoxed c -> PrimArrayBoxed d
unsafeZipWith3 f a b c = create (length a) (\n => f (index n a) (index n b) (index n c))

export
unzipWith : (a -> (b, c)) -> PrimArrayBoxed a -> (PrimArrayBoxed b, PrimArrayBoxed c)
unzipWith f arr = (map (fst . f) arr, map (snd . f) arr)

export
unzipWith3 : (a -> (b, c, d)) -> PrimArrayBoxed a -> (PrimArrayBoxed b, PrimArrayBoxed c, PrimArrayBoxed d)
unzipWith3 f arr = (map ((\(x,_,_) => x) . f) arr,
                          map ((\(_,y,_) => y) . f) arr,
                          map ((\(_,_,z) => z) . f) arr)


export
foldl : (b -> a -> b) -> b -> PrimArrayBoxed a -> b
foldl f z (MkPABoxed size arr) =
  if size == 0 then z
  else unsafePerformIO $ do
    ref <- newIORef z
    for_ [0..pred size] $ \n => do
        x <- readIORef ref
        y <- arrayDataGet n arr
        writeIORef ref (f x y)
    readIORef ref

export
foldr : (a -> b -> b) -> b -> PrimArrayBoxed a -> b
foldr f z (MkPABoxed size arr) =
  if size == 0 then z
  else unsafePerformIO $ do
    ref <- newIORef z
    for_ [pred size..0] $ \n => do
         x <- arrayDataGet n arr
         y <- readIORef ref
         writeIORef ref (f x y)
    readIORef ref

export
traverse : Applicative f => (a -> f b) -> PrimArrayBoxed a -> f (PrimArrayBoxed b)
traverse f = map fromList . traverse f . toList


||| Compares two primitive arrays for equal elements. This function assumes the
||| arrays have the same length; it must not be used in any other case.
export
unsafeEq : Eq a => PrimArrayBoxed a -> PrimArrayBoxed a -> Bool
unsafeEq a b = unsafePerformIO $
                 map (concat @{All}) $ for [0..pred (arraySize a)] $
                 \n => (==) <$> arrayDataGet n (content a) <*> arrayDataGet n (content b)
-}
