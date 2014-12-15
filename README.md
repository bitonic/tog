# Tog - A prototypical implementation of dependent types

Right now this is a laboratory to experiment in implementing dependent
types.

## Installation

    git clone https://github.com/bitonic/tog
    cd tog
    make

If you want to install the binary

    make install

## Usage

To type check files

    tog [FILE]

`tog --help` gives the full options.

See `examples/` for some example files, it's basically a simple `Agda`.

## Tests

To run the (sadly quite limited) tests, run

    make test

## Module structure

See the exported modules in the library section `tog.cabal`, each of
them should contain a brief description.  `Tog.Main` is the module that
defines main function for the `tog` executable.
