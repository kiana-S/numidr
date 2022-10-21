module Data.NumIdr.Array.Coords

import Data.Either
import Data.List
import Data.Vect
import Data.NP

%default total


-- A Nat-based range function with better semantics
export
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


--------------------------------------------------------------------------------
-- Array coordinate types
--------------------------------------------------------------------------------


||| A type-safe coordinate system for an array. The coordinates are
||| values of `Fin dim`, where `dim` is the dimension of each axis.
public export
Coords : (s : Vect rk Nat) -> Type
Coords = NP Fin

||| Forget the shape of the array by converting each index to type `Nat`.
export
toNB : Coords {rk} s -> Vect rk Nat
toNB [] = []
toNB (i :: is) = finToNat i :: toNB is


namespace Strict
  public export
  data CRange : Nat -> Type where
    One : Fin n -> CRange n
    All : CRange n
    StartBound : Fin (S n) -> CRange n
    EndBound : Fin (S n) -> CRange n
    Bounds : Fin (S n) -> Fin (S n) -> CRange n
    Indices : List (Fin n) -> CRange n
    Filter : (Fin n -> Bool) -> CRange n

  infix 0 ...
  public export
  (...) : Fin (S n) -> Fin (S n) -> CRange n
  (...) = Bounds


  public export
  CoordsRange : (s : Vect rk Nat) -> Type
  CoordsRange = NP CRange


namespace NB
  public export
  data CRangeNB : Type where
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
    newShape (r :: rs) | Left _ = newShape rs
    newShape (r :: rs) | Right xs = length xs :: newShape rs


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
  cRangeNBToList : Nat -> CRangeNB -> List Nat
  cRangeNBToList s All = range 0 s
  cRangeNBToList s (StartBound x) = range x s
  cRangeNBToList s (EndBound x) = range 0 x
  cRangeNBToList s (Bounds x y) = range x y
  cRangeNBToList s (Indices xs) = nub xs
  cRangeNBToList s (Filter p) = filter p $ range 0 s

  export
  validateCRangeNB : Nat -> CRangeNB -> Bool
  validateCRangeNB s All = True
  validateCRangeNB s (StartBound x) = x < s
  validateCRangeNB s (EndBound x) = x <= s
  validateCRangeNB s (Bounds x y) = x < s && y <= s
  validateCRangeNB s (Indices xs) = all (<s) xs
  validateCRangeNB s (Filter p) = True

  ||| Calculate the new shape given by a coordinate range.
  export
  newShape : Vect rk Nat -> Vect rk CRangeNB -> Vect rk Nat
  newShape = zipWith (length .: cRangeNBToList)

  export
  validateShape : Vect rk Nat -> Vect rk CRangeNB -> Bool
  validateShape = all id .: zipWith validateCRangeNB

  export
  getNewPos : Vect rk Nat -> Vect rk CRangeNB -> Vect rk Nat -> Vect rk Nat
  getNewPos = zipWith3 (\d,r,i => assert_total $
    case findIndex (==i) (cRangeNBToList d r) of Just x => cast x)

  export
  getCoordsList : Vect rk Nat -> Vect rk CRangeNB -> List (Vect rk Nat, Vect rk Nat)
  getCoordsList s rs = map (\is => (is, getNewPos s rs is)) $ go s rs
    where
      go : {0 rk : _} -> Vect rk Nat -> Vect rk CRangeNB -> List (Vect rk Nat)
      go [] [] = [[]]
      go (d :: s) (r :: rs) = [| cRangeNBToList d r :: go s rs |]
