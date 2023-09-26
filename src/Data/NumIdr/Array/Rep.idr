module Data.NumIdr.Array.Rep

import Data.Vect
import Data.Bits
import Data.Buffer

%default total


--------------------------------------------------------------------------------
-- Array orders
--------------------------------------------------------------------------------


||| An order is an abstract representation of the way in which array
||| elements are stored in memory. Orders are used to calculate strides,
||| which provide a method of converting an array coordinate into a linear
||| memory location.
public export
data Order : Type where
  ||| C-like order, or contiguous order. This order stores elements in a
  ||| row-major fashion (the last axis is the least significant).
  COrder : Order
  ||| Fortran-like order. This order stores elements in a column-major
  ||| fashion (the first axis is the least significant).
  FOrder : Order

%name Order o


public export
Eq Order where
  COrder == COrder = True
  FOrder == FOrder = True
  COrder == FOrder = False
  FOrder == COrder = False


||| Calculate an array's strides given its order and shape.
export
calcStrides : Order -> Vect rk Nat -> Vect rk Nat
calcStrides _      []        = []
calcStrides COrder v@(_::_)  = scanr (*) 1 $ tail v
calcStrides FOrder v@(_::_)  = scanl (*) 1 $ init v


--------------------------------------------------------------------------------
-- Array representations
--------------------------------------------------------------------------------


public export
data Rep : Type where
  Bytes : Order -> Rep
  Boxed : Order -> Rep
  Linked : Rep
  Delayed : Rep

%name Rep rep


public export
B : Rep
B = Boxed COrder

public export
L : Rep
L = Linked

public export
D : Rep
D = Delayed


public export
Eq Rep where
  Bytes o == Bytes o' = o == o'
  Boxed o == Boxed o' = o == o'
  Linked == Linked = True
  Delayed == Delayed = True
  _ == _ = False

public export
data LinearRep : Rep -> Type where
  BytesIsL : LinearRep (Bytes o)
  BoxedIsL : LinearRep (Boxed o)


public export
forceRepNC : Rep -> Rep
forceRepNC (Bytes o) = Boxed o
forceRepNC r = r

public export
mergeRep : Rep -> Rep -> Rep
mergeRep r r' = if r == Delayed || r' == Delayed then Delayed else r

public export
mergeRepNC : Rep -> Rep -> Rep
mergeRepNC r r' =
  if r == Delayed || r' == Delayed then Delayed
  else case r of
        Bytes _ => case r' of
                    Bytes o => Boxed o
                    _ => r'
        _ => r

public export
data NoConstraintRep : Rep -> Type where
  BoxedNC : NoConstraintRep (Boxed o)
  LinkedNC : NoConstraintRep Linked
  DelayedNC : NoConstraintRep Delayed

public export
mergeRepNCCorrect : (r, r' : Rep) -> NoConstraintRep (mergeRepNC r r')
mergeRepNCCorrect Delayed _ = DelayedNC
mergeRepNCCorrect (Bytes y) (Bytes x) = BoxedNC
mergeRepNCCorrect (Boxed y) (Bytes x) = BoxedNC
mergeRepNCCorrect Linked (Bytes x) = LinkedNC
mergeRepNCCorrect (Bytes y) (Boxed x) = BoxedNC
mergeRepNCCorrect (Boxed y) (Boxed x) = BoxedNC
mergeRepNCCorrect Linked (Boxed x) = LinkedNC
mergeRepNCCorrect (Bytes x) Linked = LinkedNC
mergeRepNCCorrect (Boxed x) Linked = BoxedNC
mergeRepNCCorrect Linked Linked = LinkedNC
mergeRepNCCorrect (Bytes x) Delayed = DelayedNC
mergeRepNCCorrect (Boxed x) Delayed = DelayedNC
mergeRepNCCorrect Linked Delayed = DelayedNC

public export
forceRepNCCorrect : (r : Rep) -> NoConstraintRep (forceRepNC r)
forceRepNCCorrect (Bytes x) = BoxedNC
forceRepNCCorrect (Boxed x) = BoxedNC
forceRepNCCorrect Linked = LinkedNC
forceRepNCCorrect Delayed = DelayedNC


--------------------------------------------------------------------------------
-- Byte representations of elements
--------------------------------------------------------------------------------


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


public export
RepConstraint : Rep -> Type -> Type
RepConstraint (Bytes _) a = ByteRep a
RepConstraint (Boxed _) a = ()
RepConstraint Linked a = ()
RepConstraint Delayed a = ()
