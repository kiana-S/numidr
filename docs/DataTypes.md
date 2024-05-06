# Fundamental Data Types

NumIdr exports a number of different datatypes. The most important type and the cornerstone of the library is the _array_, but there are other useful types as well.

## Arrays

### What is an Array?

In most programming languages, the word "array" is used to mean a one-dimensional list of values that is contiguous in memory. A typical array of integers may be written in list form like this:

```
[1, 4, 10, 2, -5, 18]
```

In this kind of array, elements are indexed by a single integer, starting at zero and increasing from left to right.

NumIdr, however, uses the word a bit more generally: a NumIdr array is a multi-dimensional structure that can be indexed by any number of integers. NumIdr arrays are written as nested lists:

```
[[4, -9, -2],
 [5, -6, 1]]
```

Unlike in other languages, however, this is not a nested structure. The above is a single array, and it is always manipulated as one object.

### Properties of Arrays

The `Array` datatype has the following parameters:

```idris
Array : (s : Vect rk Nat) -> (a : Type) -> Type
```

The first parameter is the _shape_, a list of numbers (the _dimensions_) where each dimension is the length of a particular _axis_ of the array. The second parameter is the _element type_, the type of the values inside the array.

Let's return to the array example from earlier:

```
[[4, -9, -2],
 [5, -6, 1]]
```

This is a rank-2 array, meaning that it has two axes. Rank-2 arrays are typically called matrices. To determine the dimensions of the array, we count the size of each nested list from the outside in, which in the case of matrices means the row axis comes before the column axis. This matrix has 2 rows and 3 columns, making its shape `[2, 3]`. Thus, a possible type for this array could be `Array [2, 3] Int`.

When determining the index of a value inside the array, the order of the indices is the same as the order of the dimensions, and each index number counts from zero. For example, the index `[1, 0]` indicates the second row and first column, which contains `5`.

> [!NOTE]
> The word "dimensions" is often ambiguously used to either refer to the rank of an array
> (as in "multi-dimensional array" in the previous section), or to the lengths of its
> axes. Conventionally, NumIdr reserves "dimension" for the second meaning, and uses
> "rank" for the first meaning.
>
> This guide has ignored this convention until now to be more understandable to newcomers,
> but will follow it from this point onward.

## Types of Arrays

Arrays are loosely divided into multiple subtypes mostly based on their rank. Each array subtype has an alias for convenience.

### Scalars

A scalar is a rank-0 array, meaning that it is indexed by 0 integers. Its alias is `Scalar`:

```idris
Scalar : (a : Type) -> Type
Scalar a = Array [] a
```

A scalar has exactly one index, the empty list `[]`. This means that it is exactly the same as a single value and as such is largely pointless, but NumIdr still provides an alias for it just in case you need it.

### Vectors

A vector is a rank-1 array:

```idris
Vector : (n : Nat) -> (a : Type) -> Type
Vector n a = Array [n] a
```

A vector's type signature and stored data is effectively identical to that of the standard library type `Vect`, whose elements are confusingly also called "vectors"; we often refer to those as "vects" to differentiate.

### Matrices

As mentioned before, a matrix is a rank-2 array:

```idris
Matrix : (m, n : Nat) -> (a : Type) -> Type
Matrix m n a = Array [m, n] a
```

There is also an alias `Matrix'` for square matrices.

```idris
Matrix' : (n : Nat) -> (a : Type) -> Type
Matrix' n a = Array [n, n] a
```

As a linear algebra library, the majority of the operations in NumIdr revolve around matrices.

#### Homogeneous Matrices

NumIdr also provides aliases for homogeneous matrices:

```idris
HMatrix : (m, n : Nat) -> (a : Type) -> Type
HMatrix m n a = Array [S m, S n] a

HMatrix' : (n : Nat) -> (a : Type) -> Type
HMatrix' n a = Array [S n, S n] a

-- To use with homogeneous matrices
HVector : (n : Nat) -> (a : Type) -> Type
HVector n a = Array [S n] a
```

These are useful for clarity when working with both homogeneous and non-homogeneous matrices.

## Other Datatypes

### Transforms

A transform is a wrapper type for a square matrix with certain properties that can be used to transform points in space.

```idris
Transform : (ty : TransType) -> (n : Nat) -> (a : Type) -> Type
```

The `TransType` parameter dictates what kind of transform it is. More information on transforms and their operations can be found in the [Transforms](Transforms.md) chapter.

### Permutations

The type `Permutation n` represents a permutation of `n` elements. Permutations are mostly used internally for various algorithms, but they are also an input in various operations, such as those that permute the axes of an array.

Permutations can be composed using `(*.)`, and a permutation can be converted into a matrix using `permuteM`.

[Contents](Intro.md) | [Next](Operations.md)
