-- Right now we diverge from Haskell and Agda in this behaviour.  It
-- probably should be fixed.
module Shadowing2 where

module One where
  postulate A : Set

module Two where
  postulate A : Set

open One
open Two

postulate foo : A

