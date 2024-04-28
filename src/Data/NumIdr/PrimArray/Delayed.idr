module Data.NumIdr.PrimArray.Delayed

import Data.List
import Data.Vect
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords
import Data.NumIdr.PrimArray.Linked

%default total

public export
PrimArrayDelayed : Vect rk Nat -> Type -> Type
PrimArrayDelayed s a = Coords s -> a


export
constant : (s : Vect rk Nat) -> a -> PrimArrayDelayed s a
constant s x _ = x


export
indexRange : {s : _} -> (rs : CoordsRange s) -> PrimArrayDelayed s a -> PrimArrayDelayed (newShape rs) a
indexRange [] v = v
indexRange (r :: rs) v with (cRangeToList r)
  _ | Left i = indexRange rs (\is' => v (assertFin i :: is'))
  _ | Right is = \(i::is') => indexRange rs (\is'' => v (assertFin (Vect.index i (fromList is)) :: is'')) is'

export
indexSetRange : {s : _} -> (rs : CoordsRange s) -> PrimArrayDelayed (newShape rs) a
                  -> PrimArrayDelayed s a -> PrimArrayDelayed s a
indexSetRange {s=[]} [] rv _ = rv
indexSetRange {s=_::_} (r :: rs) rv v with (cRangeToList r)
  _ | Left i = \(i'::is) => if i == finToNat i'
                            then indexSetRange rs rv (v . (i'::)) is
                            else v (i'::is)
  _ | Right is = \(i'::is') => case findIndex (== finToNat i') is of
    Just x => indexSetRange rs (rv . (x::)) (v . (i'::)) is'
    Nothing => v (i'::is')
