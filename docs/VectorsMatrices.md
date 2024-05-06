# Working with Vectors and Matrices

As linear algebra is one of the main concerns of NumIdr, most of its provided functions are dedicated to vectors (rank-1 arrays) and matrices (rank-2 arrays).

## The Generalized Multiplication Operator

A linear algebra library wouldn't be very useful without matrix multiplication! Since `(*)` is already used for element-wise multiplication, NumIdr defines a new interface `Mult`:

```idris
interface Mult a b c where
  (*.) : a -> b -> c

-- Synonym for homogeneous cases:
Mult' : Type -> Type
Mult' a = Mult a a a
```

The generalized multiplication operator `(*.)` covers matrix multiplication, scalar-vector multiplication, and any other operation that's vaguely multiplication-like.

## Vectors

### Algebraic Operations

Vectors can be added together with element-wise addition `(+)`. Scalar-vector multiplication is done with the generalized multiplication operator `(*.)`.

```idris
2 *. (vector [1, 1] + vector [2, 3])
  == vector [6, 8]
```

A few other basic linear algebra operations are available:

- `dot`, The dot product
- `cross`, The cross product
- `perp`, The perpendicular product (sometimes called the 2D cross product)
- `triple`, The scalar triple product

### Indexing

NumIdr provides special versions of `index` and `indexNB` and their infix forms `(!!)` and `(!?)` for use with vectors. These take a single numeric index instead of a list.

```idris
Vector.index 2 v == index [2] v

v !! 2 == v !! [2]
```

For convenience, when working with two- or three-dimensional vectors, there are postfix accessors `(.x)`, `(.y)`, and `(.z)`:

```idris
v = vector [5, 6, 2]

v.x == 5
v.y == 6
v.z == 2
```

### Other Operations

- `toVect` - Convert a vector into a `Vect`
- `dim` - Returns the vector's length
- `(++)` - Concatenate two vectors

## Matrices

### Arithmetic Operations

Like vectors, matrices can be added together using `(+)`. Matrix multiplication, as well as matrix-vector and matrix-scalar multiplication, are performed using `(*.)`.

For the purposes of working with matrices and matrix-like objects, the sub-interfaces `MultMonoid` and `MultGroup` are defined:

```idris
interface Mult' a => MultMonoid a where
  identity : a

interface MultMonoid a => MultGroup a where
  inverse : a -> a
```

The `identity` function returns an identity matrix, and `inverse` calculates a matrix's inverse. Note that `inverse` cannot tell you if an inverse of your matrix does not exist; if you want to handle that possibility, use `tryInverse` instead.

```idris
tryInverse : FieldCmp a => Matrix' n a -> Maybe (Matrix' n a)
```

You can also use the `invertible` predicate to test if a matrix has an inverse.

#### LU and LUP Decomposition

The functions `decompLU` and `decompLUP` compute LU and LUP decomposition on a matrix.

```idris
decompLU : Field a => (mat : Matrix m n a) -> Maybe (DecompLU mat)

decompLUP : FieldCmp a => (mat : Matrix m n a) -> DecompLUP mat
```

`DecompLU` and `DecompLUP` are record types holding the results of the corresponding decomposition. The accessors `lower`, `upper` and `permute` can be applied to get each component of the decomposition; `lower` and `upper` return matrices, and `permute` returns a `Permutation` value.

#### Other Algebraic Operations

- `trace` - The sum of the matrix's diagonal
- `outer` - The matrix-valued outer product (or tensor product) of two vectors
- `det` - Determinant of the matrix
- `solve` - Apply an inverse matrix to a vector, useful for solving linear equations

> [!TIP]
> The `det` and `solve` operations require computing an LUP decomposition, which can be expensive. The variants `detWithLUP` and `solveWithLUP` allow an existing LUP decomposition to be passed in, which can make your code more efficient.

### Indexing

Aside from the usual array indexing functions, there are a few functions specialized to matrix indexing:

- `getRow` and `getColumn` - Returns a specific row or column of the matrix
- `diagonal` - Returns the diagonal elements of the matrix as a vector
- `minor` - Removes a single row and column from the matrix

[Previous](Operations.md) | [Contents](Contents.md) | [Next](Transforms.md)
