module Ersatz.Number.Class 
  ( FromBit(..)
  , Summ (..), summ_cut
  )

where

import Ersatz.Bit

class FromBit a where
  fromBit :: Bit -> a

class Num a => Summ a where
  summ :: [a] -> a
  summ = sum

summ_cut cut [] = 0
summ_cut cut [x] = x
summ_cut cut xs =
  summ_cut cut $ map summ $ segments cut xs

segments cut [] = []
segments cut xs =
  let (pre,post) = splitAt cut xs
  in  pre : segments cut post


