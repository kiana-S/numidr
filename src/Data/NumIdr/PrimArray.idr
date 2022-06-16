module Data.NumIdr.PrimArray

import Data.Nat
import Data.IORef
import Data.IOArray.Prims

%default total


||| A wrapper for Idris's primitive array type.
export
record PrimArray a where
  constructor MkPrimArray
  arraySize : Nat
  content : ArrayData a

export
length : PrimArray a -> Nat
length = arraySize


-- Private helper functions for ArrayData primitives
newArrayData : Nat -> a -> IO (ArrayData a)
newArrayData n x = fromPrim $ prim__newArray (cast n) x

arrayDataGet : Nat -> ArrayData a -> IO a
arrayDataGet n arr = fromPrim $ prim__arrayGet arr (cast n)

arrayDataSet : Nat -> a -> ArrayData a -> IO ()
arrayDataSet n x arr = fromPrim $ prim__arraySet arr (cast n) x


||| Construct an array with a constant value.
export
constant : Nat -> a -> PrimArray a
constant size x = MkPrimArray size $ unsafePerformIO $ newArrayData size x

||| Construct an array from a list of "instructions" to write a
||| value to a particular index.
export
unsafeFromIns : Nat -> List (Nat, a) -> PrimArray a
unsafeFromIns size ins = unsafePerformIO $ do
    arr <- newArrayData size (believe_me ())
    for_ ins $ \(i,x) => arrayDataSet i x arr
    pure $ MkPrimArray size arr

||| Create an array given its size and a function to generate
||| its elements by its index.
export
create : Nat -> (Nat -> a) -> PrimArray a
create size f = unsafePerformIO $ do
    arr <- newArrayData size (believe_me ())
    addToArray Z size arr
    pure $ MkPrimArray size arr
  where
    addToArray : Nat -> Nat -> ArrayData a -> IO ()
    addToArray loc Z arr = pure ()
    addToArray loc (S n) arr
        = do arrayDataSet loc (f loc) arr
             addToArray (S loc) n arr

||| Index into a primitive array. This function is unsafe, as it
||| performs no boundary check on the index given.
export
index : Nat -> PrimArray a -> a
index n arr = unsafePerformIO $ arrayDataGet n $ content arr

||| A safe version of `index` that ensures the index entered is valid.
export
safeIndex : Nat -> PrimArray a -> Maybe a
safeIndex n arr = if n < length arr
                then Just $ index n arr
                else Nothing

export
copy : PrimArray a -> PrimArray a
copy arr = create (length arr) (\n => index n arr)

export
updateAt : Nat -> (a -> a) -> PrimArray a -> PrimArray a
updateAt n f arr = if n >= length arr then arr else
  unsafePerformIO $ do
    let cpy = copy arr
    x <- arrayDataGet n cpy.content
    arrayDataSet n (f x) cpy.content
    pure cpy

||| Convert a primitive array to a list.
export
toList : PrimArray a -> List a
toList arr = iter (length arr) []
  where
    iter : Nat -> List a -> List a
    iter Z acc = acc
    iter (S n) acc = let el = index n arr
                     in  iter n (el :: acc)

||| Construct a primitive array from a list.
export
fromList : List a -> PrimArray a
fromList xs = create (length xs)
    (\n => assert_total $ fromJust $ getAt n xs)
  where
    partial
    fromJust : Maybe a -> a
    fromJust (Just x) = x

||| Map a function over a primitive array.
export
map : (a -> b) -> PrimArray a -> PrimArray b
map f arr = create (length arr) (\n => f $ index n arr)


export
unsafeZipWith : (a -> b -> c) -> PrimArray a -> PrimArray b -> PrimArray c
unsafeZipWith f a b = create (length a) (\n => f (index n a) (index n b))

export
unsafeZipWith3 : (a -> b -> c -> d) ->
                 PrimArray a -> PrimArray b -> PrimArray c -> PrimArray d
unsafeZipWith3 f a b c = create (length a) (\n => f (index n a) (index n b) (index n c))

export
unzipWith : (a -> (b, c)) -> PrimArray a -> (PrimArray b, PrimArray c)
unzipWith f arr = (map (fst . f) arr, map (snd . f) arr)

export
unzipWith3 : (a -> (b, c, d)) -> PrimArray a -> (PrimArray b, PrimArray c, PrimArray d)
unzipWith3 f arr = (map ((\(x,_,_) => x) . f) arr,
                          map ((\(_,y,_) => y) . f) arr,
                          map ((\(_,_,z) => z) . f) arr)


export
foldl : (b -> a -> b) -> b -> PrimArray a -> b
foldl f z (MkPrimArray size arr) = unsafePerformIO $ do
    ref <- newIORef z
    for_ [0..pred size] $ \n => do
        x <- readIORef ref
        y <- arrayDataGet n arr
        writeIORef ref (f x y)
    readIORef ref

export
foldr : (a -> b -> b) -> b -> PrimArray a -> b
foldr f z (MkPrimArray size arr) = unsafePerformIO $ do
    ref <- newIORef z
    for_ [pred size..0] $ \n => do
         x <- arrayDataGet n arr
         y <- readIORef ref
         writeIORef ref (f x y)
    readIORef ref

export
traverse : Applicative f => (a -> f b) -> PrimArray a -> f (PrimArray b)
traverse f = map fromList . traverse f . toList


||| Compares two primitive arrays for equal elements. This function assumes
||| the arrays same the same length; it must not be used in any other case.
export
unsafeEq : Eq a => PrimArray a -> PrimArray a -> Bool
unsafeEq a b = unsafePerformIO $
                 map (concat @{All}) $ for [0..pred (arraySize a)] $
                 \n => (==) <$> arrayDataGet n (content a) <*> arrayDataGet n (content b)
