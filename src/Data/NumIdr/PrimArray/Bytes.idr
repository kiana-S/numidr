module Data.NumIdr.PrimArray.Bytes

import System
import Data.IORef
import Data.Buffer
import Data.Vect
import Data.NumIdr.Array.Coords
import Data.NumIdr.Array.Rep

%default total


export
readBuffer : ByteRep a => (i : Nat) -> Buffer -> IO a
readBuffer i buf = do
  let offset : Int = cast (i * bytes {a})
  map (fromBytes {a}) $ for range $ \n => do
    getBits8 buf $ offset + cast (finToInteger n)

export
writeBuffer : ByteRep a => (i : Nat) -> a -> Buffer -> IO ()
writeBuffer i x buf = do
  let offset = cast (i * bytes {a})
      bs = toBytes x
  n <- newIORef 0
  for_ bs $ \b => setBits8 buf (offset + !(readIORef n)) b <* modifyIORef n (+1)


public export
data PrimArrayBytes : Order -> Vect rk Nat -> Type where
  MkPABytes : (sts : Vect rk Nat) -> Buffer -> PrimArrayBytes {rk} o s

export
getBuffer : PrimArrayBytes o s -> Buffer
getBuffer (MkPABytes _ buf) = buf


fromBuffer : {o : _} -> (s : Vect rk Nat) -> Buffer -> PrimArrayBytes o s
fromBuffer s buf = MkPABytes (calcStrides o s) buf

bufferAction : {o : _} -> ByteRep a => (s : Vect rk Nat) -> (Buffer -> IO ()) -> PrimArrayBytes o s
bufferAction @{br} s action = fromBuffer s $ unsafePerformIO $ do
  Just buf <- newBuffer $ cast (product s * bytes @{br})
    | Nothing => die "Cannot create array"
  action buf
  pure buf

export
constant : {o : _} -> ByteRep a => (s : Vect rk Nat) -> a -> PrimArrayBytes o s
constant @{br} s x = bufferAction @{br} s $ \buf => do
  for_ (range 0 (product s)) $ \i => writeBuffer i x buf

export
unsafeDoIns : ByteRep a => List (Nat, a) -> PrimArrayBytes o s -> IO ()
unsafeDoIns ins (MkPABytes _ buf) = for_ ins $ \(i,x) => writeBuffer i x buf

export
unsafeFromIns : {o : _} -> ByteRep a => (s : Vect rk Nat) -> List (Nat, a) -> PrimArrayBytes o s
unsafeFromIns @{br} s ins = bufferAction @{br} s $ \buf =>
  for_ ins $ \(i,x) => writeBuffer i x buf

export
create : {o : _} -> ByteRep a => (s : Vect rk Nat) -> (Nat -> a) -> PrimArrayBytes o s
create @{br} s f = bufferAction @{br} s $ \buf => do
  for_ (range 0 (product s)) $ \i => writeBuffer i (f i) buf

export
index : ByteRep a => Nat -> PrimArrayBytes o s -> a
index i (MkPABytes _ buf) = unsafePerformIO $ readBuffer i buf

export
copy : {o,s : _} -> PrimArrayBytes o s -> PrimArrayBytes o s
copy (MkPABytes sts buf) =
  MkPABytes sts (unsafePerformIO $ do
    Just buf' <- newBuffer !(rawSize buf)
      | Nothing => die "Cannot create array"
    copyData buf 0 !(rawSize buf) buf' 0
    pure buf)

export
reorder : {o,o',s : _} -> ByteRep a => PrimArrayBytes o s -> PrimArrayBytes o' s
reorder @{br} arr@(MkPABytes sts buf) =
  if o == o' then MkPABytes sts buf
  else let sts' = calcStrides o' s
       in  unsafeFromIns @{br} s
            ((\is => (getLocation' sts' is, index @{br} (getLocation' sts is) arr))
              <$> getAllCoords' s)

export
fromList : {o : _} -> ByteRep a => (s : Vect rk Nat) -> List a -> PrimArrayBytes o s
fromList @{br} s xs = bufferAction @{br} s $ go xs 0
  where
    go : List a -> Nat -> Buffer -> IO ()
    go [] _ buf = pure ()
    go (x :: xs) i buf = writeBuffer i x buf >> go xs (S i) buf

export
foldl : {s : _} -> ByteRep a => (b -> a -> b) -> b -> PrimArrayBytes o s -> b
foldl f z (MkPABytes sts buf) =
  if product s == 0 then z
  else unsafePerformIO $ do
    ref <- newIORef z
    for_ (range 0 (product s)) $ \n => do
        x <- readIORef ref
        y <- readBuffer n buf
        writeIORef ref (f x y)
    readIORef ref

export
foldr : {s : _} -> ByteRep a => (a -> b -> b) -> b -> PrimArrayBytes o s -> b
foldr f z (MkPABytes sts buf) =
  if product s == 0 then z
  else unsafePerformIO $ do
    ref <- newIORef z
    for_ [pred $ product s..0] $ \n => do
         x <- readBuffer n buf
         y <- readIORef ref
         writeIORef ref (f x y)
    readIORef ref

export
traverse : {o,s : _} -> ByteRep a => ByteRep b => Applicative f => (a -> f b) -> PrimArrayBytes o s -> f (PrimArrayBytes o s)
traverse f = map (Bytes.fromList _) . traverse f . foldr (::) []
