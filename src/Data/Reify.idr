module Data.Reify

%default total


public export
data Reify : a -> Type where
  MkReify : (x : a) -> Reify x

public export
getReify : {0 x : a} -> Reify x -> a
getReify (MkReify x) = x

