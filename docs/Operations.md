# Basic Operations on Arrays

> [!CAUTION]
> Arrays and their associated functions are not intended to be evaluated at compile-time. If you try to compute an array in the REPL, you will not get the output you expect!
>
> If you really need to use the REPL to test array code, use `:exec`.

## Constructing Arrays

The most important array constructor is `array`, which returns an array of the specified values:

```idris
array [[1, 2, 3], [4, 5, 6]]
```

Scalars, vectors and matrices have their own constructors, used in exactly the same way (`scalar`, `vector`, and `matrix`). These should be used instead of `array` wherever possible, as they provide more information to the type-checker.

There are also a few other, more basic constructors for convenience.

```idris
-- A 2x2x3 array filled with zeros
repeat 0 [2, 2, 3]

-- Same as previous
zeros [2, 2, 3]

-- A 2x2x3 array filled with ones
ones [2, 2, 3]
```

## Accessing Array Properties

There are a few simple functions for accessing basic properties of arrays: `shape` and `rank`, which are self-explanatory, and `size`, which returns the total number of elements in the array.

> [!TIP]
> The `shape` accessor is sufficient for most uses, but it can cause problems with the type-checker, as for an array `arr : Array s a` the type checker does not know that `shape arr` and `s` are equal. To solve this problem, you can use the `ShapeView`:
>
> ```idris
> example {s} arr with (viewShape arr)
>   _ | Shape s = ...
> ```

## Indexing Arrays

NumIdr provides multiple different indexing functions for different purposes. These functions can be grouped based on these categories:

**Operation**
- **Access** - Accesses and returns elements from the array.
- **Update** - Returns a new array with the specified element or range updated by a function. These are indicated by an `Update` suffix.
- **Set** - Returns a new array with the specified element or range set to new values. These are indicated by a `Set` suffix.

**Range**
- **Default** - Operates on a single array element.
- **Range** - Operates on multiple elements at once. These are indicated by a `Range` suffix.

**Safety**
- **Safe** - Guarantees through its type that the index is within range by requiring each index to be a `Fin` value.
- **Non-Bounded** - Does not guarantee through its type that the index is within range, and returns `Nothing` if the provided index is out of bounds. These are indicated by an `NB` suffix.
- **Unsafe** - Does not perform any bounds checks at all. These are indicated by an `Unsafe` suffix. **Only use these if you really know what you are doing!**

Not all combinations of these categories are defined by the library. Here are the currently provided indexing functions:

|            | Safe            | Ranged Safe            | Non-Bounded       | Ranged Non-Bounded       | Unsafe                | Ranged Unsafe                |
|------------|-----------------|------------------------|-------------------|--------------------------|-----------------------|------------------------------|
| **Access** | `index`, `(!!)` | `indexRange`, `(!!..)` | `indexNB`, `(!?)` | `indexRangeNB`, `(!?..)` | `indexUnsafe`, `(!#)` | `indexRangeUnsafe`, `(!#..)` |
| **Update** | `indexUpdate`   | `indexUpdateRange`     | `indexUpdateNB`   |                          |                       |                              |
| **Set**    | `indexSet`      | `indexSetRange`        | `indexSetNB`      |                          |                       |                              |

The accessor functions have operator forms for convenience.

### Specifying Coordinates

When indexing a single element, a coordinate is specified as a list of numbers, where each number is either a `Fin` value for safe indexing or a `Nat` value for non-bounded and unsafe indexing.

```idris
index [1, 0] arr

-- Equivalent operator form
arr !! [1, 0]
```

With ranged indexing, a sub-array of the original array is accessed or modified. This sub-array is given by a list of _range specifiers_, one for each axis, which can be one of the following:

- `Bounds x y` - Every index from `x` (inclusive) to `y` (exclusive)
- `StartBound x` - Every index from `x` to the end of the axis
- `EndBound y` - Every index from the start of the axis to `y`
- `One i`, `One' i` - The single index `i`
- `All` - Every index in the axis
- `Indices xs` - A list of indices in the axis
- `Filter p` - A predicate specifying which indices to access or modify

The range specifier `One` is special, as it is the only range specifier that decreases the rank of the resulting array. For example, the following matrix access returns the first column as a vector due to `One` being used:

```idris
matrix [[2, 0], [1, 2]] !!.. [All, One 0]
  == vector [2, 1]
```

`One'` does not decrease the rank of the result in this way.

## Standard Interface Methods

The array type implements a number of standard interfaces. Most of these implementations are unremarkable, but a few have caveats that are worth noting.

### Numeric Operations

Arrays implement the numeric interfaces (`Num`, `Neg`, `Fractional`), as well as `Semigroup` and `Monoid`, if their element type supports those operations. These functions are computed elementwise.

```idris
matrix [[1, 1], [2, 5]] + matrix [[2, 3], [-1, 3]]
 == matrix [[3, 4], [1, 8]]
```

This elementwise behavior holds for `(+)`, `(*)`, `(-)`, `(/)`, and `(<+>)`. **`(*)` is not matrix multiplication!** For the generalized multiplication operator, which includes matrix multiplication, see [the next chapter](VectorsMatrices.md).

> [!WARNING]
> Due to unfortunate restrictions in Idris's standard `Num` interface, `(+)` and `(*)` can only be used when the array's shape is available at run-time. If this is not the case, you must use `zipwith (+)` or `zipWith (*)` instead.

### `Foldable` and `Traversable`

When folding or traversing the elements of an array, these elements are ordered in row-major or "C-style" order, which corresponds to the order in which elements are written and displayed. This behavior should not be depended on, however, as it can change based on the internal [array representation](Representations.md); use the `elements` function if you specifically want row-major order.

## Other Common Operations

### Concatenation and Stacking

Two arrays can be concatenated along an axis (`concat`), so long as all other axes have the same dimensions. Two matrices being concatenated along the row axis requires that they must have the same number of columns.

```idris
-- 0 is the first axis i.e. the row axis
concat 0 (matrix [[1, 2], [3, 4]]) (matrix [[5, 6], [7, 8]])
  == matrix [[1, 2],
             [3, 4],
             [5, 6],
             [7, 8]]
```

Stacking (`stack`) is similar to concatenation, but slightly different. Stacking combines arrays with the exact same shape into a single array that is one rank higher. For example, vectors can be stacked along the row axis to obtain a matrix whose rows are the original vectors.

```idris
stack 0 [vector [1, 2], vector [3, 4]]
  == matrix [[1, 2],
             [3, 4]]
```

There are also specialized functions for operating on vectors and matrices: `(++)` for concatenating vectors; `vconcat` and `hconcat` for concatenating two matrices vertically (by row) and horizontally (by column) respectively, and `vstack` and `hstack` for stacking row vectors and column vectors respectively.

### Reshaping and Resizing

An array can be "reshaped" into any other shape, so long as the total number of elements is the same. This reshaping is done by arranging the elements into a linear order before inserting them into the new array. As with folding, the default order is row-major.

```idris
reshape [3, 2] (vector [1, 2, 3, 4, 5, 6])
  == matrix [[1, 2],
             [3, 4],
             [5, 6]]
```

Arrays can also be resized with `resize`, which changes their shape while keeping every element at the same index. A default element must be provided to fill any indices that did not exist in the original array.

```idris
resize [2, 4] 10 (matrix [[1, 2],
                          [3, 4],
                          [5, 6]])
  == matrix [[1, 2, 10, 10],
             [3, 4, 10, 10]]
```

Instead of the `resize` function, one can also use the `resizeLTE` function, which does not require a default element, but only works if the new array would be provably smaller than the original one.

### Transpose

The `transpose` function reverses the axis order of an array: For `arr : Array [3,2,4] Int`, we have `transpose arr : Array [4,2,3] Int`. For matrices, this corresponds to the usual definition of switching rows and columns. There is also a postfix form `(.T)`.

For more fine-grained control when rearranging arrays, there are the `swapAxes` and `permuteAxes` functions, where the first swaps only two axes and the second takes an arbitrary [permutation](DataTypes.md#Permutations). There are also `swapInAxis` and `permuteInAxis`, which permute inside an axis, e.g. swapping rows or columns in a matrix.

Like with concatenation and stacking, the swap and permute functions have forms specific to vectors and matrices: `swapCoords` and `permuteCoords` for vectors, and `swapRows`, `permuteRows`, `swapColumns`, and `permuteColumns` for matrices.

[Previous](DataTypes.md) | [Contents](Contents.md) | [Next](VectorsMatrices.md)
