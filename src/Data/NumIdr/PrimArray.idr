module Data.NumIdr.PrimArray

import Data.IOArray.Prims

%default total

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


export
unsafeFromIns : Nat -> List (Nat, a) -> PrimArray a
unsafeFromIns size ins = unsafePerformIO $ do
    arr <- newArrayData size (believe_me ())
    for_ ins $ \(i,x) => arrayDataSet i x arr
    pure $ MkPrimArray size arr

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


export
unsafeIndex : Nat -> PrimArray a -> a
unsafeIndex n arr = unsafePerformIO $ arrayDataGet n $ content arr

export
index : Nat -> PrimArray a -> Maybe a
index n arr = if n < length arr
                then Just $ unsafeIndex n arr
                else Nothing


export
toList : PrimArray a -> List a
toList arr = iter (length arr) []
  where
    iter : Nat -> List a -> List a
    iter Z acc = acc
    iter (S n) acc = let el = unsafeIndex n arr
                     in  iter n (el :: acc)

export
fromList : List a -> PrimArray a
fromList xs = create (length xs)
    (\n => assert_total $ fromJust $ getAt n xs)
  where
    partial
    fromJust : Maybe a -> a
    fromJust (Just x) = x

export
map : (a -> b) -> PrimArray a -> PrimArray b
map f arr = create (length arr) (\n => f $ unsafeIndex n arr)

