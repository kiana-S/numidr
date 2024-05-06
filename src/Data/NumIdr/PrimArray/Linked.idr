module Data.NumIdr.PrimArray.Linked

import Data.Vect
import Data.DPair
import Data.NumIdr.Array.Rep
import Data.NumIdr.Array.Coords

%default total


export
constant : (s : Vect rk Nat) -> a -> Vects s a
constant [] x = x
constant (d :: s) xs = replicate d (constant s xs)

export
index : Coords s -> Vects s a -> a
index [] x = x
index (c :: cs) xs = index cs (index c xs)

export
update : Coords s -> (a -> a) -> Vects s a -> Vects s a
update [] f v = f v
update (i :: is) f v = updateAt i (update is f) v

export
indexRange : {s : _} -> (rs : CoordsRange s) -> Vects s a -> Vects (newShape rs) a
indexRange [] v = v
indexRange (r :: rs) v with (cRangeToList r)
  _ | Left i = indexRange rs (Vect.index (assertFin i) v)
  _ | Right is = assert_total $
        case toVect _ (map (\i => indexRange rs (Vect.index (assertFin i) v)) is) of
          Just v => v

export
indexSetRange : {s : _} -> (rs : CoordsRange s) -> Vects (newShape rs) a -> Vects s a -> Vects s a
indexSetRange {s=[]} [] rv _ = rv
indexSetRange {s=_::_} (r :: rs) rv v with (cRangeToList r)
  _ | Left i = updateAt (assertFin i) (indexSetRange rs rv) v
  _ | Right is = foldl (\v,i => updateAt (assertFin i) (indexSetRange rs (Vect.index (assertFin i) rv)) v) v is


export
fromFunction : {s : _} -> (Coords s -> a) -> Vects s a
fromFunction {s = []} f = f []
fromFunction {s = d :: s} f = tabulate (\i => fromFunction (f . (i::)))

export
fromFunctionNB : {s : _} -> (Vect rk Nat -> a) -> Vects {rk} s a
fromFunctionNB {s = []} f = f []
fromFunctionNB {s = d :: s} f = tabulate' {n=d} (\i => fromFunctionNB (f . (i::)))
  where
    tabulate' : forall a. {n : _} -> (Nat -> a) -> Vect n a
    tabulate' {n=Z} f = []
    tabulate' {n=S _} f = f Z :: tabulate' (f . S)

export
mapVects : {s : _} -> (a -> b) -> Vects s a -> Vects s b
mapVects {s = []} f x = f x
mapVects {s = _ :: _} f v = Prelude.map (mapVects f) v

export
foldl : {s : _} -> (b -> a -> b) -> b -> Vects s a -> b
foldl {s=[]} f z v = f z v
foldl {s=_::_} f z v = Prelude.foldl (Linked.foldl f) z v

export
foldr : {s : _} -> (a -> b -> b) -> b -> Vects s a -> b
foldr {s=[]} f z v = f v z
foldr {s=_::_} f z v = Prelude.foldr (flip $ Linked.foldr f) z v

export
traverse : {s : _} -> Applicative f => (a -> f b) -> Vects s a -> f (Vects s b)
traverse {s=[]} f v = f v
traverse {s=_::_} f v = Prelude.traverse (Linked.traverse f) v
