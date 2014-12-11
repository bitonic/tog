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

There are various options, most notably `-i` to get a GHCi-like prompt,
and `-d` to get debug output.  `-d ''` will give you a complete dump of
all the debug output, that is to say a lot of stuff.

`tog --help` gives the full options.

See `examples/` for some example files, it's basically a simple `Agda`.

## Tests

To run the (sadly quite limited) tests, run

    make test

## Module structure

Only the top-level modules are supposed to be imported.  Some of them,
we often import qualified.  If you wanted to import everything:

    import qualified Abstract
    import CheckFile
    import Elaborate
    import Error
    import Instrumentation
    import Main
    import Monad
    import Names
    import Parse
    import PrettyPrint
    import qualified Raw
    import ScopeCheck
    import Syntax
    import Term
    import TogPrelude
    import TypeCheck
    import Unify

The exception are modules that ideally wouldn't be in this repo, namely
`Data.Collect`.