module Data.NumIdr.PrimArray.Bytes

import System
import Data.IORef
import Data.Bits
import Data.So
import Data.Buffer
import Data.Vect
import Data.NumIdr.Array.Coords
import Data.NumIdr.Array.Rep

%default total


public export
interface ByteRep a where
  bytes : Nat

  toBytes : a -> Vect bytes Bits8
  fromBytes : Vect bytes Bits8 -> a

export
ByteRep Bits8 where
  bytes = 1

  toBytes x = [x]
  fromBytes [x] = x

export
ByteRep Bits16 where
  bytes = 2

  toBytes x = [cast (x `shiftR` 8), cast x]
  fromBytes [b1,b2] = cast b1 `shiftL` 8 .|. cast b2

export
ByteRep Bits32 where
  bytes = 4

  toBytes x = [cast (x `shiftR` 24),
               cast (x `shiftR` 16),
               cast (x `shiftR` 8),
               cast x]
  fromBytes [b1,b2,b3,b4] =
    cast b1 `shiftL` 24 .|.
    cast b2 `shiftL` 16 .|.
    cast b3 `shiftL` 8 .|.
    cast b4

export
ByteRep Bits64 where
  bytes = 8

  toBytes x = [cast (x `shiftR` 56),
               cast (x `shiftR` 48),
               cast (x `shiftR` 40),
               cast (x `shiftR` 32),
               cast (x `shiftR` 24),
               cast (x `shiftR` 16),
               cast (x `shiftR` 8),
               cast x]
  fromBytes [b1,b2,b3,b4,b5,b6,b7,b8] =
    cast b1 `shiftL` 56 .|.
    cast b2 `shiftL` 48 .|.
    cast b3 `shiftL` 40 .|.
    cast b4 `shiftL` 32 .|.
    cast b5 `shiftL` 24 .|.
    cast b6 `shiftL` 16 .|.
    cast b7 `shiftL` 8 .|.
    cast b8

export
ByteRep Int where
  bytes = 8

  toBytes x = [cast (x `shiftR` 56),
               cast (x `shiftR` 48),
               cast (x `shiftR` 40),
               cast (x `shiftR` 32),
               cast (x `shiftR` 24),
               cast (x `shiftR` 16),
               cast (x `shiftR` 8),
               cast x]
  fromBytes [b1,b2,b3,b4,b5,b6,b7,b8] =
    cast b1 `shiftL` 56 .|.
    cast b2 `shiftL` 48 .|.
    cast b3 `shiftL` 40 .|.
    cast b4 `shiftL` 32 .|.
    cast b5 `shiftL` 24 .|.
    cast b6 `shiftL` 16 .|.
    cast b7 `shiftL` 8 .|.
    cast b8

export
ByteRep Int8 where
  bytes = 1

  toBytes x = [cast x]
  fromBytes [x] = cast x

export
ByteRep Int16 where
  bytes = 2

  toBytes x = [cast (x `shiftR` 8), cast x]
  fromBytes [b1,b2] = cast b1 `shiftL` 8 .|. cast b2

export
ByteRep Int32 where
  bytes = 4

  toBytes x = [cast (x `shiftR` 24),
               cast (x `shiftR` 16),
               cast (x `shiftR` 8),
               cast x]
  fromBytes [b1,b2,b3,b4] =
    cast b1 `shiftL` 24 .|.
    cast b2 `shiftL` 16 .|.
    cast b3 `shiftL` 8 .|.
    cast b4

export
ByteRep Int64 where
  bytes = 8

  toBytes x = [cast (x `shiftR` 56),
               cast (x `shiftR` 48),
               cast (x `shiftR` 40),
               cast (x `shiftR` 32),
               cast (x `shiftR` 24),
               cast (x `shiftR` 16),
               cast (x `shiftR` 8),
               cast x]
  fromBytes [b1,b2,b3,b4,b5,b6,b7,b8] =
    cast b1 `shiftL` 56 .|.
    cast b2 `shiftL` 48 .|.
    cast b3 `shiftL` 40 .|.
    cast b4 `shiftL` 32 .|.
    cast b5 `shiftL` 24 .|.
    cast b6 `shiftL` 16 .|.
    cast b7 `shiftL` 8 .|.
    cast b8

export
ByteRep Bool where
  bytes = 1

  toBytes b = [if b then 1 else 0]
  fromBytes [x] = x /= 0

export
ByteRep a => ByteRep b => ByteRep (a, b) where
  bytes = bytes {a} + bytes {a=b}

  toBytes (x,y) = toBytes x ++ toBytes y
  fromBytes = bimap fromBytes fromBytes . splitAt _

export
{n : _} -> ByteRep a => ByteRep (Vect n a) where
  bytes = n * bytes {a}

  toBytes xs = concat $ map toBytes xs
  fromBytes {n = 0} bs = []
  fromBytes {n = S n} bs =
    let (bs1, bs2) = splitAt _ bs
    in  fromBytes bs1 :: fromBytes bs2


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
  let size = product s
  for_ [0..pred size] $ \i => writeBuffer i x buf

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
  let size = product s
  for_ [0..pred size] $ \i => writeBuffer i (f i) buf

export
index : ByteRep a => Nat -> PrimArrayBytes o s -> a
index i (MkPABytes _ buf) = unsafePerformIO $ readBuffer i buf

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
