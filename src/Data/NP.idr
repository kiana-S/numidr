module Data.NP

import Data.Vect

%default total


public export
data NP : (f : k -> Type) -> (ts : Vect n k) -> Type where
  Nil  : NP {k} f []
  (::) : f t -> NP {k} f ts -> NP {k} f (t :: ts)


public export
(all : NP (Eq . f) ts) => Eq (NP f ts) where
  (==) {all=[]} [] [] = True
  (==) {all=_::_} (x :: xs) (y :: ys) = (x == y) && (xs == ys)

public export
(all : NP (Show . f) ts) => Show (NP f ts) where
  show xs = "[" ++ elems xs ++ "]"
    where
      elems : {0 f,ts : _} -> (all : NP (Show . f) ts) => NP f ts -> String
      elems {all=[]} [] = ""
      elems {all=[_]} [x] = show x
      elems {all=_::_} (x :: xs) = show x ++ ", " ++ elems xs



public export
head : NP f (t :: ts) -> f t
head (x :: _) = x

public export
index : (i : Fin n) -> NP {n} f ts -> f (index i ts)
index FZ (x :: xs) = x
index (FS i) (x :: xs) = index i xs
