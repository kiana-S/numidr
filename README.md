# NumIdr

NumIdr is a linear algebra and data manipulation library for Idris 2. It features
an efficient, type-safe array data structure, as well as utilities for working with
vector spaces and matrices. It borrows concepts heavily from Python's [NumPy](https://numpy.org/),
as well as Rust's [nalgebra](https://www.nalgebra.org/).

The name is pronounced like "num-idge".

## Features

- A type-safe and efficient array type, based on NumPy's arrays.

- Compile-time checked indexing operations to avoid run-time overhead.

- Utility functions and operations for working with vectors, matrices,
  homogeneous coordinates, and other linear algebra computations.

- Transform types for working with rotations, reflections, isometries, and other
  types of affine maps.

## Planned Features

- An IO-based mutable array type, useful for writing more efficient code.

## Documentation

Most of the exported utility functions have docstrings. There are also plans for
an in-depth tutorial on NumIdr's features, though that is not available yet.

## Usage

Basic package install:

``` shell
idris2 --install numidr.ipkg
```

