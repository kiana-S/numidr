module Data.NumIdr.Array.Coords

import Data.Either
import Data.List
import Data.List1
import Data.Vect

import public Data.Vect.Quantifiers

%default total


-- A Nat-based range function with better semantics
public export
range : Nat -> Nat -> List Nat
range x y = if x < y then assert_total $ takeBefore (>= y) (countFrom x S)
                     else []

-- helpful theorems for working with ranges

export
rangeLen : (x,y : Nat) -> length (range x y) = minus y x
rangeLen x y = believe_me $ Refl {x = minus y x}

export
rangeLenZ : (x : Nat) -> length (range 0 x) = x
rangeLenZ x = rangeLen 0 x `trans` minusZeroRight x

export %unsafe
assertFin : Nat -> Fin n
assertFin n = natToFinLt n @{believe_me Oh}

--------------------------------------------------------------------------------
-- Array coordinate types
--------------------------------------------------------------------------------


||| A type-safe coordinate system for an array. The coordinates are
||| values of `Fin dim`, where `dim` is the dimension of each axis.
public export
Coords : (s : Vect rk Nat) -> Type
Coords = All Fin


-- Occasionally necessary for reasons of Idris not being great at
-- resolving interface constraints
public export
[eqCoords] Eq (Coords s) where
  [] == [] = True
  (x :: xs) == (y :: ys) = x == y && xs == ys


||| Forget the shape of the array by converting each index to type `Nat`.
export
toNB : Coords {rk} s -> Vect rk Nat
toNB [] = []
toNB (i :: is) = finToNat i :: toNB is

export
validateCoords : (s : Vect rk Nat) -> Vect rk Nat -> Maybe (Coords s)
validateCoords [] [] = Just []
validateCoords (d :: s) (i :: is) = (::) <$> natToFin i d <*> validateCoords s is


namespace Strict
  public export
  data CRange : Nat -> Type where
    One : Fin n -> CRange n
    One' : Fin n -> CRange n
    All : CRange n
    StartBound : Fin (S n) -> CRange n
    EndBound : Fin (S n) -> CRange n
    Bounds : Fin (S n) -> Fin (S n) -> CRange n
    Indices : List (Fin n) -> CRange n
    Filter : (Fin n -> Bool) -> CRange n


  public export
  CoordsRange : (s : Vect rk Nat) -> Type
  CoordsRange = All CRange


namespace NB
  public export
  data CRangeNB : Type where
    One : Nat -> CRangeNB
    One' : Nat -> CRangeNB
    All : CRangeNB
    StartBound : Nat -> CRangeNB
    EndBound : Nat -> CRangeNB
    Bounds : Nat -> Nat -> CRangeNB
    Indices : List Nat -> CRangeNB
    Filter : (Nat -> Bool) -> CRangeNB


--------------------------------------------------------------------------------
-- Indexing helper functions
--------------------------------------------------------------------------------


public export
Vects : Vect rk Nat -> Type -> Type
Vects []     a = a
Vects (d::s) a = Vect d (Vects s a)

export
collapse : {s : _} -> Vects s a -> List a
collapse {s=[]} = pure
collapse {s=_::_} = concat . map collapse


export
mapWithIndex : {s : Vect rk Nat} -> (Vect rk Nat -> a -> b) -> Vects s a -> Vects s b
mapWithIndex {s=[]}   f x = f [] x
mapWithIndex {s=_::_} f v = mapWithIndex' (\i => mapWithIndex (\is => f (i::is))) v
  where
    mapWithIndex' : {0 a,b : Type} -> (Nat -> a -> b) -> Vect n a -> Vect n b
    mapWithIndex' f [] = []
    mapWithIndex' f (x::xs) = f Z x :: mapWithIndex' (f . S) xs


export
getLocation' : (sts : Vect rk Nat) -> (is : Vect rk Nat) -> Nat
getLocation' = sum .: zipWith (*)

||| Compute the memory location of an array element
||| given its coordinate and the strides of the array.
export
getLocation : Vect rk Nat -> Coords {rk} s -> Nat
getLocation sts is = getLocation' sts (toNB is)


namespace Strict
  public export
  cRangeToList : {n : Nat} -> CRange n -> Either Nat (List Nat)
  cRangeToList (One x) = Left (cast x)
  cRangeToList (One' x) = Right [cast x]
  cRangeToList All = Right $ range 0 n
  cRangeToList (StartBound x) = Right $ range (cast x) n
  cRangeToList (EndBound x) = Right $ range 0 (cast x)
  cRangeToList (Bounds x y) = Right $ range (cast x) (cast y)
  cRangeToList (Indices xs) = Right $ map cast $ nub xs
  cRangeToList (Filter p) = Right $ map cast $ filter p $ toList Fin.range


  public export
  newRank : {s : _} -> CoordsRange s -> Nat
  newRank [] = 0
  newRank (r :: rs) = case cRangeToList r of
                        Left _ => newRank rs
                        Right _ => S (newRank rs)

  ||| Calculate the new shape given by a coordinate range.
  public export
  newShape : {s : _} -> (rs : CoordsRange s) -> Vect (newRank rs) Nat
  newShape [] = []
  newShape (r :: rs) with (cRangeToList r)
    _ | Left _ = newShape rs
    _ | Right xs = length xs :: newShape rs


  getNewPos : {s : _} -> (rs : CoordsRange {rk} s) -> Vect rk Nat -> Vect (newRank rs) Nat
  getNewPos [] [] = []
  getNewPos (r :: rs) (i :: is) with (cRangeToList r)
    _ | Left _ = getNewPos rs is
    _ | Right xs = cast (assert_total $ case findIndex (==i) xs of Just x => x)
                    :: getNewPos rs is

  export
  getCoordsList : {s : Vect rk Nat} -> (rs : CoordsRange s) -> List (Vect rk Nat, Vect (newRank rs) Nat)
  getCoordsList rs = map (\is => (is, getNewPos rs is)) $ go rs
    where
      go : {0 rk : _} -> {s : Vect rk Nat} -> CoordsRange s -> List (Vect rk Nat)
      go [] = [[]]
      go (r :: rs) = [| (either pure id (cRangeToList r)) :: go rs |]


namespace NB
  export
  validateCRange : (s : Vect rk Nat) -> Vect rk CRangeNB -> Maybe (CoordsRange s)
  validateCRange [] [] = Just []
  validateCRange (d :: s) (r :: rs) = [| validate' d r :: validateCRange s rs |]
    where
      validate' : (n : Nat) -> CRangeNB -> Maybe (CRange n)
      validate' n (One i) =
        case isLT i n of
          Yes _ => Just (One (natToFinLT i))
          _ => Nothing
      validate' n (One' i) =
        case isLT i n of
          Yes _ => Just (One' (natToFinLT i))
          _ => Nothing
      validate' n All = Just All
      validate' n (StartBound x) =
        case isLTE x n of
          Yes _ => Just (StartBound (natToFinLT x))
          _ => Nothing
      validate' n (EndBound x) =
        case isLTE x n of
          Yes _ => Just (EndBound (natToFinLT x))
          _ => Nothing
      validate' n (Bounds x y) =
        case (isLTE x n, isLTE y n) of
          (Yes _, Yes _) => Just (Bounds (natToFinLT x) (natToFinLT y))
          _ => Nothing
      validate' n (Indices xs) = Indices <$> traverse
        (\x => case isLT x n of
                Yes _ => Just (natToFinLT x)
                No _ => Nothing) xs
      validate' n (Filter f) = Just (Filter (f . finToNat))

  export %unsafe
  assertCRange : (s : Vect rk Nat) -> Vect rk CRangeNB -> CoordsRange s
  assertCRange [] [] = []
  assertCRange (d :: s) (r :: rs) = assert' r :: assertCRange s rs
    where
      assert' : forall n. CRangeNB -> CRange n
      assert' (One i) = One (assertFin i)
      assert' (One' i) = One' (assertFin i)
      assert' All = All
      assert' (StartBound x) = StartBound (assertFin x)
      assert' (EndBound x) = EndBound (assertFin x)
      assert' (Bounds x y) = Bounds (assertFin x) (assertFin y)
      assert' (Indices xs) = Indices (assertFin <$> xs)
      assert' (Filter f) = Filter (f . finToNat)

  public export
  cRangeNBToList : Nat -> CRangeNB -> Either Nat (List Nat)
  cRangeNBToList s (One i) = Left i
  cRangeNBToList s (One' i) = Right [i]
  cRangeNBToList s All = Right $ range 0 s
  cRangeNBToList s (StartBound x) = Right $ range x s
  cRangeNBToList s (EndBound x) = Right $ range 0 x
  cRangeNBToList s (Bounds x y) = Right $ range x y
  cRangeNBToList s (Indices xs) = Right $ nub xs
  cRangeNBToList s (Filter p) = Right $ filter p $ range 0 s

  public export
  newRank : Vect rk Nat -> Vect rk CRangeNB -> Nat
  newRank _ [] = 0
  newRank (d :: s) (r :: rs) =
    case cRangeNBToList d r of
      Left _ => newRank s rs
      Right _ => S (newRank s rs)

  ||| Calculate the new shape given by a coordinate range.
  public export
  newShape : (s : Vect rk Nat) -> (is : Vect rk CRangeNB) -> Vect (newRank s is) Nat
  newShape [] [] = []
  newShape (d :: s) (r :: rs) with (cRangeNBToList d r)
    _ | Left _ = newShape s rs
    _ | Right xs = length xs :: newShape s rs

export
getAllCoords' : Vect rk Nat -> List (Vect rk Nat)
getAllCoords' = traverse (\case Z => []; S n => [0..n])

export
getAllCoords : (s : Vect rk Nat) -> List (Coords s)
getAllCoords [] = [[]]
getAllCoords (Z :: s) = []
getAllCoords (S d :: s) = [| forget (allFins d) :: getAllCoords s |]
