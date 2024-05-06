# Transforms

In code that works with linear algebra, it is common to use matrices as _transformations_, i.e. functions that take in a vector and output a new vector. These matrices can often be divided into categories based on the operations they perform, such as a rotation matrix or an affine transformation matrix.

The `Transform` wrapper exists to encode these differing properties on the type level, as well as to provide extra utilities for working with matrices in this fashion.

## Types of Transforms

`Transform` has the following type signature:

```idris
Transform : (ty : TransType) -> (n : Nat) -> (a : Type) -> Type
```

A `Transform ty n a` is a wrapper over an `HMatrix' n a`. The `ty` parameter is the transform type, which dictates what properties the transform has. These eight options are currently available:

**Affine Types:**
- `TAffine`
- `TIsometry` (rotation + reflection + translation)
- `TRigid` (rotation + translation)
- `TTranslation`

**Linear Types:**
- `TLinear`
- `TOrthonormal` (rotation + reflection)
- `TRotation`
- `TTrivial` (always the `identity`)

The capital T at the beginning of each of these names identifies it as a `TransType` value. To make working with transforms smoother, NumIdr provides synonyms for transforms of each type. For example, `Isometry n a` is a synonym for `Transform TIsometry n a`.

### Linear and Affine

Transform types are divided into linear and affine types. Linear transforms must preserve the origin point, whereas affine transforms do not have this restriction.

Linear and affine transform types are in a one-to-one correspondence: a linear transform can be converted to and from an affine transform by adding or removing a translation component.

```
Linear      <-> Affine
Orthonormal <-> Isometry
Rotation    <-> Rigid
Trivial     <-> Translation
```

The `setTranslation` and `linearize` functions perform these conversions.

For simplicity, both categories of transform are wrappers over homogeneous matrices, even though linear transforms could be represented by non-homogeneous matrices.

### Transform Type Casting

Some transform types can be cast into other types. For example, a `Rotation` can be cast into an `Orthonormal`, as all rotation matrices are orthonormal.

```idris
rot : Rotation 3 Double

cast rot : Orthonormal 3 Double
```

In the diagram from the previous section, lower types can be cast into types higher up. Each linear type (on the left) can also be cast into the corresponding affine type (on the right).

## Constructing Transforms

There are multiple ways to construct transforms, either by wrapping a matrix or directly through constructor functions.

For each transform type, `fromHMatrix` can be used to test if a homogeneous matrix satisfies the right properties, and converts it into a transform if it does. The `Rotation`, `Orthonormal` and `Linear` types also have `fromMatrix` for non-homogeneous matrices.

> [!NOTE]
> The `fromHMatrix` and `fromMatrix` constructors use exact equality comparisons when testing matrices, which can be an issue if your element type is `Double` or a similar inexact number type. To remedy this, NumIdr provides a `WithEpsilon` named implementation that defines equality approximately.
>
> ```idris
> fromHMatrix @{WithEpsilon 1.0e-6} mat
> ```

There are also direct constructors for transforms, which are often more convenient as they do not have the possibility of failing. There are too many of these constructors to exhaustively list here, so I encourage you to look through the functions in the `Data.NumIdr.Transform.*` modules to see what is available.

## Multiplication with Transforms

Like most objects in NumIdr, transforms multiply with the generalized multiplication operator `(*.)`, and `identity` and `inverse` can also be used with transforms. There is no `tryInverse` function, as all transforms are required to be invertible.

Transforms of any types can be multiplied. When two transforms of different types are multiplied, the resulting transform type is determined by taking the most specific type that both original types can be cast to. For example, an `Orthonormal` transform multiplied by a `Translation` returns an `Isometry`.

### The Point Type

Transforms behave differently from regular matrices when applied to vectors. When an affine transform is applied in this way, it is first linearized, so that vectors only have linear transforms applied to them. **This is not a bug!**

In order to properly apply affine transforms, the `Point` type must be used, which is a wrapper around the `Vector` type that supports these transforms. A point can be constructed with the `point` function, which is used exactly the same as the `vector` constructor.

```idris
point [4, 3, 6]
```

Points support most basic operations that vectors do, including indexing operations and standard library methods. However, a point cannot be added to another point. Instead, a vector must be added to a point:

```idris
(+.) : Vector n a -> Point n a -> Point n a

(.+) : Point n a -> Vector n a -> Point n a

(-.) : Point n a -> Point n a -> Vector n a
```

To remember the distinction between the two addition operators, the dot is always on the side of the point, not the vector.

This separation between points and vectors is intended to make working with affine transformations more convenient, as it mirrors the separation between points and vectors in affine algebra. These may feel like arbitrary restrictions, but you might be surprised by how convenient they are to work with!

[Previous](VectorsMatrices.md) | [Contents](Intro.md)
