# Tog - A prototypical implementation of dependent types

Right now this is a laboratory to experiment in implementing dependent
types.

## Installation

    git clone https://github.com/bitonic/tog
    cd tog
    make all

If you want to install the binary add

    cabal install

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

Top-level module interface:

    import           Conf
    import           PrettyPrint
    import           Syntax
    import qualified Syntax.Raw                       as SR
    import qualified Syntax.Internal                  as SI
    import           Term
    import qualified Term.Context                     as Ctx
    import qualified Term.Substitution                as Sub
    import qualified Term.Telescope                   as Tel
    import           TypeCheck3
