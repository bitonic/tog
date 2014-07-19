{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module PrettyPrint
  ( module Text.PrettyPrint.Leijen
  , render
  , renderPretty
  , renderCompact
  , ($$)
  , ($$>)
  , (//)
  , (//>)
  , defaultShow
  , condParens
  , parens
  , Pretty(..)
  , list
  ) where

import           Data.String                      (IsString(fromString))
import qualified Text.PrettyPrint.Leijen          as PP
import           Text.PrettyPrint.Leijen          hiding ((<$>), (<$$>), renderPretty, renderCompact, Pretty(..), list, parens, tupled)

render :: Pretty a => a -> String
render x = defaultShow 0 x ""

renderPretty :: Pretty a => Int -> a -> String
renderPretty width_ x =
  displayS (PP.renderPretty 0.7 width_ (pretty x)) ""

renderCompact :: Pretty a => a -> String
renderCompact x = displayS (PP.renderCompact (pretty x)) ""

infixr 5 $$
infixr 5 $$>

infixr 6 //
infixr 6 //>

list :: [Doc] -> Doc
list [] = "[]"
list xs = group $ PP.encloseSep ("[" <> space) (line <> "]") ("," <> space) xs

tupled :: [Doc] -> Doc
tupled = encloseSep lparen rparen (comma <> space)

-- | Hard break
($$) :: Doc -> Doc -> Doc
x $$ y = x <> line <> y

-- | Hard break with indent
($$>) :: Doc -> Doc -> Doc
x $$> y = x <> nest 2 (line <> y)

-- | Soft break
(//) :: Doc -> Doc -> Doc
x // y = x <> group (line <> y)

-- | Soft break with indent
(//>) :: Doc -> Doc -> Doc
x //> y = x <> group (nest 2 (line <> y))

defaultShow :: Pretty a => Int -> a -> ShowS
defaultShow p = displayS . PP.renderPretty 0.7 80 . prettyPrec p

condParens :: Bool -> Doc -> Doc
condParens True  = parens
condParens False = id

parens :: Doc -> Doc
parens x = char '(' <> align x <> char ')'

instance IsString Doc where
  fromString = text

class Pretty a where
  {-# MINIMAL pretty | prettyPrec #-}

  pretty :: a -> Doc
  pretty = prettyPrec 0

  prettyList :: [a] -> Doc
  prettyList  = encloseSep lbracket rbracket (comma <> space) . map pretty

  prettyPrec :: Int -> a -> Doc
  prettyPrec _ = pretty

instance Pretty a => Pretty [a] where
  pretty        = prettyList

instance Pretty Doc where
  pretty        = id

instance Pretty () where
  pretty ()     = text "()"

instance Pretty Bool where
  pretty b      = bool b

instance Pretty Char where
  pretty c      = char c
  prettyList s  = string s

instance Pretty Int where
  pretty i      = int i

instance Pretty Integer where
  pretty i      = integer i

instance Pretty Float where
  pretty f      = float f

instance Pretty Double where
  pretty d      = double d

instance (Pretty a,Pretty b) => Pretty (a,b) where
  pretty (x,y)  = tupled [pretty x, pretty y]

instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
  pretty (x,y,z)= tupled [pretty x, pretty y, pretty z]

instance Pretty a => Pretty (Maybe a) where
  pretty Nothing        = empty
  pretty (Just x)       = pretty x
