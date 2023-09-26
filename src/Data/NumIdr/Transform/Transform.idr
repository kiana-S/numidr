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


||| A transform type encodes the properties of a transform. There are 8 transform
||| types, and together with the coersion relation `(:<)` they form a semilattice.
export
TransType : Type
TransType = (Fin 4, Bool)

namespace TransType
  public export
  TAffine, TIsometry, TRigid, TTranslation,
    TLinear, TOrthonormal, TRotation, TTrivial : TransType
  TAffine = (3, True)
  TIsometry = (2, True)
  TRigid = (1, True)
  TTranslation = (0, True)
  TLinear = (3, False)
  TOrthonormal = (2, False)
  TRotation = (1, False)
  TTrivial = (0, False)


--------------------------------------------------------------------------------
-- Transformation type operations
--------------------------------------------------------------------------------


||| Coersion relation for transform types.
||| `a :< b` is `True` if and only if any transform of type `a` can be cast into
||| a transform of type `b`.
public export
(:<) : TransType -> TransType -> Bool
(xn, xb) :< (yn, yb) = (xn <= yn) && (xb <= yb)

||| Return the type of transform resulting from multiplying transforms of
||| the two input types.
public export
transMult : TransType -> TransType -> TransType
transMult (xn, xb) (yn, yb) = (max xn yn, xb || yb)

||| Return the linearized transform type, i.e. the transform type resulting
||| from removing the translation component of the original transform.
public export
linearizeType : TransType -> TransType
linearizeType = mapSnd (const False)

||| Return the delinearized transform type, i.e. the transform type resulting
||| from adding a translation to the original transform.
public export
delinearizeType : TransType -> TransType
delinearizeType = mapSnd (const True)


||| A transform is a wrapper for a homogeneous matrix subject to certain
||| restrictions, such as a rotation, an isometry, or a rigid transform.
||| The restriction on the transform is encoded by the transform's *type*.
|||
||| Transforms have special behavior over matrices when it comes to multiplication.
||| When a transform is applied to a vector, only the linear part of the transform
||| is applied, as if `linearize` were called on the transform before the operation.
|||
||| In order for non-linear transformations to be used, the transform should be
||| applied to the special wrapper type `Point`. This separates the concepts of
||| point and vector, which is often useful when working with affine maps.
export
data Transform : TransType -> Nat -> Type -> Type where
  MkTrans : (ty : TransType) -> HMatrix' n a -> Transform ty n a

%name Transform t


export
unsafeMkTrans : {ty : _} -> HMatrix' n a -> Transform ty n a
unsafeMkTrans = MkTrans _


||| Unwrap the inner homogeneous matrix from a transform.
export
getHMatrix : Transform ty n a -> HMatrix' n a
getHMatrix (MkTrans _ mat) = mat

||| Unwrap the inner matrix from a transform, ignoring the translation component
||| if one exists.
export
getMatrix : Transform ty n a -> Matrix' n a
getMatrix (MkTrans _ mat) = getMatrix mat

export
convertRep : (rep : Rep) -> RepConstraint rep a => Transform ty n a -> Transform ty n a
convertRep rep (MkTrans _ mat) = MkTrans _ (convertRep rep mat)

||| Linearize a transform by removing its translation component.
||| If the transform is already linear, then this function does nothing.
export
linearize : Num a => Transform ty n a -> Transform (linearizeType ty) n a
linearize {n} (MkTrans _ mat) with (viewShape mat)
  _ | Shape [S n,S n] = MkTrans _ (hmatrix (getMatrix mat) (zeros _))

||| Set the translation component of a transform.
|||
||| `setTranslation v tr == translate v *. linearize tr`
|||
||| If `tr` is linear:
||| `setTranslation v tr == translate v *. tr`
export
setTranslation : Num a => Vector n a -> Transform ty n a
                  -> Transform (delinearizeType ty) n a
setTranslation v (MkTrans _ mat) = MkTrans _ (hmatrix (getMatrix mat) v)


namespace Vector
  export
  applyInv : FieldCmp a => Transform ty n a -> Vector n a -> Vector n a
  applyInv tr v = assert_total $ case solve (getMatrix tr) v of Just v' => v'

namespace Point
  export
  applyInv : FieldCmp a => Transform ty n a -> Point n a -> Point n a
  applyInv (MkTrans _ mat) p = assert_total $
    case solve (getMatrix mat) (zipWith (-) (toVector p) (getTranslationVector mat)) of
      Just v => fromVector v


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
