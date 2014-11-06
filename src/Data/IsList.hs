-- | Compatibility module for GHC 7.6.3
module Data.IsList where

class IsList l where
  type Item l
  fromList  :: [Item l] -> l
  toList    :: l -> [Item l]
