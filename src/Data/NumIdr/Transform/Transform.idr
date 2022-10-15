module Data.NumIdr.Transform.Transform

import Data.Vect
import Data.NumIdr.Interfaces
import Data.NumIdr.Array
import Data.NumIdr.Vector
import Data.NumIdr.Matrix
import Data.NumIdr.Homogeneous
import Data.NumIdr.Transform.Point

%default total


--------------------------------------------------------------------------------
-- Transformation Types
--------------------------------------------------------------------------------


public export
data TransType = TAffine | TIsometry | TRigid | TTranslation
               | TLinear | TOrthonormal | TRotation | TTrivial

%name TransType ty


public export
Show TransType where
  show TAffine = "TAffine"
  show TIsometry = "TIsometry"
  show TRigid = "TRigid"
  show TTranslation = "TTranslation"
  show TLinear = "TLinear"
  show TOrthonormal = "TOrthonormal"
  show TRotation = "TRotation"
  show TTrivial = "TTrivial"


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


--------------------------------------------------------------------------------
-- Transformation type operations
--------------------------------------------------------------------------------


public export
(:<) : TransType -> TransType -> Bool
x :< y with (toSignature x, toSignature y)
  _ | ((xn, xb), (yn, yb)) = (xn <= yn) && (xb >= yb)

public export
transMult : TransType -> TransType -> TransType
transMult x y with (toSignature x, toSignature y)
  _ | ((xn, xb), (yn, yb)) = fromSignature (max xn yn, xb && yb)

public export
linearizeType : TransType -> TransType
linearizeType = fromSignature . mapSnd (const False) . toSignature


export
data Transform : TransType -> Nat -> Type -> Type where
  MkTrans : (type : TransType) -> HMatrix' n a -> Transform type n a

%name Transform t


export
unsafeMkTrans : {ty : _} -> HMatrix' n a -> Transform ty n a
unsafeMkTrans = MkTrans _

export
toHMatrix : Transform ty n a -> HMatrix' n a
toHMatrix (MkTrans _ mat) = mat

export
linearize : Num a => Transform ty n a -> Transform (linearizeType ty) n a
linearize {n} (MkTrans _ mat) with (viewShape mat)
  _ | Shape [S n,S n] = MkTrans _ (hmatrix (getMatrix mat) (zeros _))


--------------------------------------------------------------------------------
-- Interface implementations
--------------------------------------------------------------------------------


mulPoint : Num a => HMatrix' n a -> Point n a -> Point n a
mulPoint mat p = fromVector $ zipWith (+) (getMatrix mat *. toVector p)
                                          (getTranslationVector mat)

mulVector : Num a => HMatrix' n a -> Vector n a -> Vector n a
mulVector mat v = getMatrix mat *. v

export
Num a => Mult (Transform ty n a) (Point n a) (Point n a) where
  MkTrans _ mat *. p = mulPoint mat p

export
Num a => Mult (Transform ty n a) (Vector n a) (Vector n a) where
  MkTrans _ mat *. v = mulVector mat v


export
Num a => Mult (Transform t1 n a) (Transform t2 n a) (Transform (transMult t1 t2) n a) where
  MkTrans _ m1 *. MkTrans _ m2 = MkTrans _ (m1 *. m2)

export
[TransformMult'] Num a => Mult (Transform ty n a) (Transform ty n a) (Transform ty n a) where
  MkTrans _ m1 *. MkTrans _ m2 = MkTrans _ (m1 *. m2)


export
{n,ty : _} -> Num a => MultMonoid (Transform ty n a) using TransformMult' where
  identity = MkTrans ty identity

export
{n,ty : _} -> FieldCmp a => MultGroup (Transform ty n a) where
  inverse (MkTrans _ mat) = MkTrans _ (inverse mat)


export
{t2 : _} -> So (t1 :< t2) => Cast a b => Cast (Transform t1 n a) (Transform t2 n b) where
  cast (MkTrans t1 mat) = MkTrans t2 (cast mat)

export
Show a => Show (Transform ty n a) where
  showPrec p (MkTrans ty mat) = showCon p "MkTrans" $ showArg ty ++ showArg mat
