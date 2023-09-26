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
    for_ (range 0 (product s)) $ \i => arrayDataSet i (f i) arr

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
  for_ (range 0 (product s)) $ \i => arrayDataSet i !(readBuffer i buf) arr
  pure arr

export
boxedToBytes : {s : _} -> ByteRep a => PrimArrayBoxed o s a -> PrimArrayBytes o s
boxedToBytes @{br} (MkPABoxed sts arr) = MkPABytes sts $ unsafePerformIO $ do
  Just buf <- newBuffer $ cast (product s * bytes @{br})
    | Nothing => die "Cannot create array"
  for_ (range 0 (product s)) $ \i => writeBuffer i !(arrayDataGet i arr) buf
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
    for_ (range 0 (product s)) $ \n => do
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
    for_ (range 0 (product s)) $ \n => do
         x <- arrayDataGet n arr
         y <- readIORef ref
         writeIORef ref (f x y)
    readIORef ref

export
traverse : {o,s : _} -> Applicative f => (a -> f b) -> PrimArrayBoxed o s a -> f (PrimArrayBoxed o s b)
traverse f = map (Boxed.fromList _) . traverse f . foldr (::) []

