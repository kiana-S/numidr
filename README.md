# NumIdr

NumIdr is a linear algebra and data manipulation library for Idris 2. It features
an efficient, type-safe array data structure, as well as utilities for working with
vector spaces and matrices.

The name is pronounced like "num-idge".

## Features

- A type-safe and efficient array type, based on NumPy's arrays.

- Compile-time checked indexing operations to avoid run-time overhead.

- Utility functions and operations for working with vectors, matrices,
  homogeneous coordinates, and other linear algebra computations.

- Transform types for working with rotations, reflections, isometries, and other
  types of affine maps.

## Inspiration

NumIdr is inspired by many different data science and linear algebra libraries,
including Python's [NumPy](https://numpy.org/), Rust's [nalgebra](https://www.nalgebra.org/),
and Haskell's [massiv](https://hackage.haskell.org/package/massiv). It aims to
combine the most useful features of each library.

## Documentation

Most of the exported utility functions have docstrings. There is also
a (currently unfinished) guide on how to use NumIdr [here](docs/Intro.md).

## Usage

To install using idris2 directly:

``` sh
git clone https://github.com/kiana-S/numidr
cd numidr
idris2 --install numidr.ipkg

```

Or you can install using pack:

``` sh
pack install numidr
```
