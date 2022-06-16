module Data.NumIdr.Array.Coords

import Data.Either
import Data.Vect
import public Data.NP

%default total


namespace Coords

  ||| A type-safe coordinate system for an array. The coordinates are
  ||| values of `Fin dim`, where `dim` is the dimension of each axis.
  public export
  Coords : (s : Vect rk Nat) -> Type
  Coords = NP Fin

  ||| Forget the shape of the array by converting each index to type `Nat`.
  export
  toNats : Coords {rk} s -> Vect rk Nat
  toNats [] = []
  toNats (i :: is) = finToNat i :: toNats is


  public export
  Vects : Vect rk Nat -> Type -> Type
  Vects []     a = a
  Vects (d::s) a = Vect d (Vects s a)

  export
  collapse : {s : _} -> Vects s a -> List a
  collapse {s=[]} = pure
  collapse {s=_::_} = concat . map collapse


  export
  mapWithIndex : {s : Vect rk Nat} -> (Vect rk Nat -> a -> b) -> Vects {rk} s a -> Vects s b
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
  getLocation sts is = getLocation' sts (toNats is)


namespace CoordsRange

  public export
  data CRange : Nat -> Type where
    One : Fin n -> CRange n
    All : CRange n
    StartBound : Fin (S n) -> CRange n
    EndBound : Fin (S n) -> CRange n
    Bounds : Fin (S n) -> Fin (S n) -> CRange n

  infix 0 ...

  public export
  (...) : Fin (S n) -> Fin (S n) -> CRange n
  (...) = Bounds


  public export
  CoordsRange : (s : Vect rk Nat) -> Type
  CoordsRange = NP CRange

  public export
  cRangeToBounds : {n : Nat} -> CRange n -> Either Nat (Nat, Nat)
  cRangeToBounds (One x) = Left (cast x)
  cRangeToBounds All = Right (0, n)
  cRangeToBounds (StartBound x) = Right (cast x, n)
  cRangeToBounds (EndBound x) = Right (0, cast x)
  cRangeToBounds (Bounds x y) = Right (cast x, cast y)


  public export
  newRank : {s : _} -> CoordsRange s -> Nat
  newRank [] = 0
  newRank (r :: rs) = case cRangeToBounds r of
                        Left _ => newRank rs
                        Right _ => S (newRank rs)

  ||| Calculate the new shape given by a coordinate range.
  public export
  newShape : {s : _} -> (rs : CoordsRange s) -> Vect (newRank rs) Nat
  newShape [] = []
  newShape (r :: rs) with (cRangeToBounds r)
    newShape (r :: rs) | Left _ = newShape rs
    newShape (r :: rs) | Right (x,y) = minus y x :: newShape rs


  getNewPos : {s : _} -> (rs : CoordsRange {rk} s) -> Vect rk Nat -> Vect (newRank rs) Nat
  getNewPos [] [] = []
  getNewPos (r :: rs) (i :: is) with (cRangeToBounds r)
    getNewPos (r :: rs) (i :: is) | Left _ = getNewPos rs is
    getNewPos (r :: rs) (i :: is) | Right (x, _) = minus i x :: getNewPos rs is

  export
  getCoordsList : {s : Vect rk Nat} -> (rs : CoordsRange s) -> List (Vect rk Nat, Vect (newRank rs) Nat)
  getCoordsList rs = map (\is => (is, getNewPos rs is)) $ go rs
    where
      go : {0 rk : _} -> {s : Vect rk Nat} -> CoordsRange s -> List (Vect rk Nat)
      go [] = pure []
      go (r :: rs) = [| (case cRangeToBounds r of
                           Left x => pure x
                           Right (x,y) => [x,S x..pred y]) :: go rs |]
