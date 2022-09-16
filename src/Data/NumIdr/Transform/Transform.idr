module Data.NumIdr.Transform.Transform

import Data.Vect
import Data.NumIdr.Interfaces
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Matrix
import Data.NumIdr.Homogeneous
import Data.NumIdr.Transform.Point

public export
data TransType = TAffine | TIsometry | TRigid | TTranslation
               | TLinear | TOrthonormal | TRotation | TTrivial


-- Lower numbers can be coerced to higher numbers
toSignature : TransType -> (Fin 4, Bool)
toSignature TAffine = (3, True)
toSignature TIsometry = (2, True)
toSignature TRigid = (1, True)
toSignature TTranslation = (0, True)
toSignature TLinear = (3, False)
toSignature TOrthonormal = (2, False)
toSignature TRotation = (1, False)
toSignature TTrivial = (0, False)

public export
fromSignature : (Fin 4, Bool) -> TransType
fromSignature (3, True) = TAffine
fromSignature (2, True) = TIsometry
fromSignature (1, True) = TRigid
fromSignature (0, True) = TTranslation
fromSignature (3, False) = TLinear
fromSignature (2, False) = TOrthonormal
fromSignature (1, False) = TRotation
fromSignature (0, False) = TTrivial

public export
(:<) : TransType -> TransType -> Bool
x :< y with (toSignature x, toSignature y)
  _ | ((xn, xb), (yn, yb)) = (xn <= yn) && (xb >= yb)

public export
transMult : TransType -> TransType -> TransType
transMult x y with (toSignature x, toSignature y)
  _ | ((xn, xb), (yn, yb)) = fromSignature (max xn yn, xb && yb)

public export
linearize : TransType -> TransType
linearize = fromSignature . mapSnd (const False) . toSignature

export
data Transform : TransType -> Nat -> Type -> Type where
  MkTrans : (type : TransType) -> HMatrix' n a -> Transform type n a


mulPoint : Num a => HMatrix' n a -> Point n a -> Point n a
mulPoint m p = fromVector $ zipWith (+) (getMatrix m *. toVector p)
                                        (getTranslationVector m)

mulVector : Num a => HMatrix' n a -> Vector n a -> Vector n a
mulVector m v = getMatrix m *. v

export
Num a => Mult (Transform type n a) (Point n a) (Point n a) where
  MkTrans _ m *. p = mulPoint m p

export
Num a => Mult (Transform type n a) (Vector n a) (Vector n a) where
  MkTrans _ m *. v = mulVector m v

export
Num a => Mult (Transform t1 n a) (Transform t2 n a) (Transform (transMult t1 t2) n a) where
  MkTrans _ m1 *. MkTrans _ m2 = MkTrans _ (m1 *. m2)

export
{t2 : _} -> So (t1 :< t2) => Cast (Transform t1 n a) (Transform t2 n a) where
  cast (MkTrans t1 m) = MkTrans t2 m
