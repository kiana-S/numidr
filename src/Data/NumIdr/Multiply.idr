module Data.NumIdr.Multiply

%default total


infixr 9 *.

||| A generalized multiplication/transformation operator. This interface is
||| necessary since the standard multiplication operator is homogenous.
public export
interface Mult a b where
  0 Result : Type
  (*.) : a -> b -> Result
