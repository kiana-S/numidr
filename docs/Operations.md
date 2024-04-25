# Basic Operations on Arrays

## Constructing Arrays

The most important array constructor is `array`, which returns an array of the specified values:

```idris
array [[1, 2, 3], [4, 5, 6]]
```

Scalars, vectors and matrices have their own constructors, used in exactly the same way (`scalar`, `vector`, and `matrix`). These should be used instead of `array` whenever possible, as they provide more information to the type-checker.

There are also a few other, more basic constructors for convenience.

```idris
-- A 2x2x3 array filled with zeros
repeat 0 [2, 2, 3]

-- Same as previous
zeros [2, 2, 3]

-- A 2x2x3 array filled with ones
ones [2, 2, 3]
```

## Indexing Arrays

NumIdr provides multiple different indexing functions for different purposes. These functions can be grouped based on these categories:

**Operation**
- Access - Accesses and returns elements from the array.
- Update - Returns a new array with the specified element or range updated by a function. These are indicated by an `Update` suffix.
- Set - Returns a new array with the specified element or range set to new values. These are indicated by a `Set` suffix.

**Range**
- Default - Operates on a single array element.
- Range - Operates on multiple elements at once. These are indicated by a `Range` suffix.

**Safety**
- Safe - Guarantees through its type that the index is within range by requiring each index to be a `Fin` value.
- Non-Bounded - Does not guarantee through its type that the index is within range, and returns `Nothing` if the provided index is out of bounds. These are indicated by an `NB` suffix.
- Unsafe - Does not perform any bounds checks at all. These are indicated by an `Unsafe` suffix. **Only use these if you really know what you are doing!**

Not all combinations of these categories are defined by the library. Here are the currently provided indexing functions:

|            | Safe            | Ranged Safe            | Non-Bounded       | Ranged Non-Bounded       | Unsafe                | Ranged Unsafe                |
|------------|-----------------|------------------------|-------------------|--------------------------|-----------------------|------------------------------|
| **Access** | `index`, `(!!)` | `indexRange`, `(!!..)` | `indexNB`, `(!?)` | `indexRangeNB`, `(!?..)` | `indexUnsafe`, `(!#)` | `indexRangeUnsafe`, `(!#..)` |
| **Update** | `indexUpdate`   | `indexUpdateRange`     | `indexUpdateNB`   |                          |                       |                              |
| **Set**    | `indexSet`      | `indexSetRange`        | `indexSetNB`      |                          |                       |                              |

The accessor functions also have operator forms.

### Specifying Coordinates

When indexing a single element, a coordinate is specified as a list of numbers, where each number is either a `Fin` value for safe indexing or a `Nat` value for non-bounded and unsafe indexing.

```idris
index [1, 0] arr

-- Equivalent operator form
arr !! [1, 0]
```

With ranged indexing, a sub-array of the original array is accessed or modified. This sub-array is given by a list of _range specifiers_, one for each axis, which can be one of the following:

- `Bounds x y` - Every index from `x` to `y`
- `StartBound x` - Every index from `x` to the end of the axis
- `EndBound y` - Every index from the start of the axis to `y`
- `All` - Every index in the axis
- `Indices xs` - A list of indices in the axis
- `Filter p` - A predicate specifying which indices to access or modify

There is also an extra specifier, `One i`, that selects exactly one index of the axis. It is only usable in safe indexing, and it is notable for being the only range specifier that decreases the rank of the sub-array. For example, the following matrix access returns the first column as a vector due to `One` being used:

```idris
matrix [[2, 0], [1, 2]] !!.. [All, One 0]
  == vector [2, 1]
```

[Previous](DataTypes.md) | [Contents](Intro.md) | [Next](VectorsMatrices.md)
