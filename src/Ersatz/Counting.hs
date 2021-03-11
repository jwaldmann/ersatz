{- | Counting predicates.

Semantics:
compare the number of true bits in @bs@ with a constant @k@

first argument @k@ can be negative,
or larger than @length bs@.

Implementation: binary summation, using a balanced tree,
with intermediate results using the bit width required for @k@
and an overflow indicator bit.

-}

{-# language KindSignatures, DataKinds, TypeApplications, ScopedTypeVariables, RankNTypes, LambdaCase, TypeFamilies #-}

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

-- | Numbers with bounded bit width and overflow detection.
-- Semantics for arithmetical operations
-- (currently, only addition is implemented)
-- if no overflow, then contents is correct.
-- if overflow, then contents is arbvitrary.
-- Application: for bit width 1, the (only) contents bit
-- of the sum is the Or (instead of the Xor) of inputs.
-- This should help propagation in the at-most-one constraint.
data Bits (w :: Nat) =
  Bits { contents :: [Bit] -- ^ will have length <= w
       , overflow :: Bit
       }

instance KnownNat w => Codec (Bits w) where
  type Decoded (Bits w) = Integer
  decode s b = decode s (overflow b) >>= \ case
    False -> decode s (B.Bits $ contents b)
    True -> error "overflow"
  encode n = fromBits $ encode n

fromBits :: forall w . KnownNat w => B.Bits -> Bits w
fromBits (B.Bits bs) =
  let w = fromIntegral $ natVal @w undefined
      (small, large) = splitAt w bs
  in  Bits { contents = small
           , overflow = or large
           }

instance KnownNat w => Num (Bits w) where
  a + b =
    let w = fromIntegral $ natVal @w undefined
    in  if w == 1
        then let ha = head $ contents a <> [false]
                 hb = head $ contents b <> [false]
             in Bits { contents = [ ha || hb ]
                     , overflow =
                       overflow a || overflow b || (ha && hb)
                     }
        else
          let c = fromBits @w
               $ (B.Bits $ contents a) + (B.Bits $ contents b)
          in  c { overflow =
                  overflow a || overflow b || overflow c
                }

sumBits :: KnownNat w => [Bit] -> Bits w
sumBits [] = fromBits $ B.Bits []
sumBits [b] = fromBits $ B.Bits [b]
sumBits bs =
  let (pre, post) = splitAt (div (length bs) 2) bs
  in  sumBits pre + sumBits post
