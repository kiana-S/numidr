module Data.NP

import Data.Vect

%default total


public export
data NP : (f : k -> Type) -> (ts : Vect n k) -> Type where
  Nil  : NP {k} f []
  (::) : f t -> NP {k} f ts -> NP {k} f (t :: ts)


public export
(all : NP (Eq . f) ts) => Eq (NP f ts) where
  (==) {all = []} [] [] = True
  (==) {all = _ :: _} (x :: xs) (y :: ys) = (x == y) && (xs == ys)



public export
index : (i : Fin n) -> NP {n} f ts -> f (index i ts)
index FZ (x :: xs) = x
index (FS i) (x :: xs) = index i xs
