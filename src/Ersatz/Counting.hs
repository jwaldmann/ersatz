{- | Counting predicates.

Semantics:
compare the number of true bits in @bs@ with a constant @k@

first argument @k@ can be negative,
or larger than @length bs@.

Implementation: binary summation, using a balanced tree,
with intermediate results using the bit width required for @k@
and an overflow indicator bit.

-}

{-# language KindSignatures, DataKinds, TypeApplications, ScopedTypeVariables, RankNTypes #-}

module Ersatz.Counting where

import Prelude hiding (and,or,not,(||),(&&))
import Ersatz.Bit
import qualified Ersatz.Bits as B
import Ersatz.Codec
import Ersatz.Equatable
import Ersatz.Orderable

import GHC.TypeLits
import Data.Proxy
import Data.Reflection
import Data.List (genericLength)

exactly :: Int -> [ Bit ] -> Bit
exactly k bs | k < 0 = false
exactly 0 bs = not $ or bs
exactly k bs =
  if 2*k > length bs
  -- prefer to compare with the number that has shorter bit length.
  -- do NOT use 2*k >= length bs  since this
  -- leads to infinite recursion in case of equality.
  then exactly (length bs - k) $ map not bs
  else eqSumBits (encode $ fromIntegral k) bs

atmost :: Int -> [ Bit ] -> Bit
atmost k bs | k < 0 = false
atmost 0 bs = not $ or bs
atmost k bs =
  if 2*k > length bs
  then atleast (length bs - k) $ map not bs
  else geqSumBits (encode $ fromIntegral k) bs

atleast :: Int -> [ Bit ] -> Bit
atleast k _  | k <= 0 = true
atleast 1 bs = or bs
atleast k bs =
  if 2*k > length bs
  then atmost (length bs - k) $ map not bs
  else leqSumBits (encode $ fromIntegral k) bs

eqSumBits x@(B.Bits xs) bs =
  reifyNat (genericLength xs) $ \ ( _ :: KnownNat w => Proxy w) ->
    let b = sumBits @w bs
    in  x === B.Bits (contents b) && not (overflow b)

geqSumBits x@(B.Bits xs) bs =
  reifyNat (genericLength xs) $ \ ( _ :: KnownNat w => Proxy w) ->
    let b = sumBits @w bs
    in  x >=? B.Bits (contents b) && not (overflow b)

leqSumBits x@(B.Bits xs) bs =
  reifyNat (genericLength xs) $ \ ( _ :: KnownNat w => Proxy w) ->
    let b = sumBits @w bs
    in  x <=? B.Bits (contents b) || overflow b  

data Bits (w :: Nat) =
  Bits { contents :: [Bit] -- ^ will have length <= w
       , overflow :: Bit
       }

fromBits :: forall w . KnownNat w => [Bit] -> Bits w
fromBits bs =
  let w = fromIntegral $ natVal @w undefined
      (small, large) = splitAt w bs
  in  Bits { contents = small
           , overflow = or large
           }

instance KnownNat w => Num (Bits w) where
  a + b =
    let B.Bits cs = B.Bits (contents a) + B.Bits (contents b)
        c = fromBits @w cs
    in  c { overflow = overflow a || overflow b || overflow c }    

sumBits :: KnownNat w => [Bit] -> Bits w
sumBits [] = fromBits []
sumBits [b] = fromBits [b]
sumBits bs =
  let (pre, post) = splitAt (div (length bs) 2) bs
  in  sumBits pre + sumBits post
