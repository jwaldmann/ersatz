{- | Counting predicates.

Semantics:
compare the number of true bits in @bs@ with a constant @k@

first argument @k@ can be negative,
or larger than @length bs@.

Implementation: summation, using a balanced tree.
Intermediate results use the bit width required for @k@,
and an overflow indicator bit.
Intermediate results are represented in unary for small @k@, else binary.

-}

{-# language DataKinds, TypeApplications, ScopedTypeVariables, RankNTypes, TypeFamilies, AllowAmbiguousTypes #-}

module Ersatz.Counting where

import Prelude hiding (and,or,not,(||),(&&))
import Ersatz.Bit
import Ersatz.Bits
import Ersatz.Number.Class
import qualified Ersatz.Number.Binary as B
import qualified Ersatz.Number.Unary as U
import Ersatz.Codec
import Ersatz.Equatable
import Ersatz.Orderable
import Ersatz.Problem (runSAT',dimacsClauses,dimacsNumVariables)
import Ersatz.Variable (exists)

import GHC.TypeLits
import Data.Proxy
import Data.Kind
import Data.Reflection
import Data.List (genericLength)
import Control.Monad (replicateM)
import Text.Printf
import qualified Data.IntSet as I

-- FIXME explain these numbers, and verify their explanation.
-- I think I compared the literal-size of the CNFs, see cnfsize below.
-- use_unary _ _ = False
use_unary k n =  k == 1
           || k == 2 && n < 438
           || k == 3 && n < 71
           || k == 4 && n < 192
           || k == 5 && n < 83
           || n <= 50
           
exactly :: Int -> [ Bit ] -> Bit
exactly k bs | k < 0 = false
exactly 0 bs = not $ or bs
exactly k bs =
  let n = length bs in
  if 2*k > n
  -- prefer to compare with the smaller number
  -- do NOT use 2*k >= length bs  since this
  -- leads to infinite recursion in case of equality.
  then exactly (n - k) $ map not bs
  else if use_unary k n
       then eqSumBitsU (fromIntegral k) bs
       else eqSumBitsB (fromIntegral k) bs

atmost :: Int -> [ Bit ] -> Bit
atmost k bs | k < 0 = false
atmost 0 bs = not $ or bs
atmost k bs =
  let n = length bs in
  if 2*k > n
  then atleast (n - k) $ map not bs
  else if use_unary k n
       then geqSumBitsU (fromIntegral k) bs
       else geqSumBitsB (fromIntegral k) bs

atleast :: Int -> [ Bit ] -> Bit
atleast k _  | k <= 0 = true
atleast 1 bs = or bs
atleast k bs =
  let n = length bs in
  if 2*k > n
  then atmost (n - k) $ map not bs
  else if use_unary k n
       then leqSumBitsU (fromIntegral k) bs
       else leqSumBitsB (fromIntegral k) bs

eqSumBitsB :: Integer -> [Bit] -> Bit
eqSumBitsB x bs = 
  let Bits xs = encode x
  in  reifyNat (genericLength xs)
      $ \ ( _ :: KnownNat w => Proxy w) ->
          encode x === count @(B.Binary w) bs

leqSumBitsB :: Integer -> [Bit] -> Bit
leqSumBitsB x bs = 
  let Bits xs = encode x
  in  reifyNat (genericLength xs)
      $ \ ( _ :: KnownNat w => Proxy w) ->
          encode x <=? count @(B.Binary w) bs

geqSumBitsB :: Integer -> [Bit] -> Bit
geqSumBitsB x bs = 
  let Bits xs = encode x
  in  reifyNat (genericLength xs)
      $ \ ( _ :: KnownNat w => Proxy w) ->
          encode x >=? count @(B.Binary w) bs

eqSumBitsU :: Integer -> [Bit] -> Bit
eqSumBitsU x bs = 
  reifyNat (x+1)
      $ \ ( _ :: KnownNat w => Proxy w) ->
          encode x === count @(U.Unary w) bs

leqSumBitsU :: Integer -> [Bit] -> Bit
leqSumBitsU x bs = 
  reifyNat (x+1)
      $ \ ( _ :: KnownNat w => Proxy w) ->
          encode x <=? count @(U.Unary w) bs

geqSumBitsU :: Integer -> [Bit] -> Bit
geqSumBitsU x bs = 
  reifyNat (x+1)
      $ \ ( _ :: KnownNat w => Proxy w) ->
          encode x >=? count @(U.Unary w) bs

count :: (FromBit n, Summ n) => [Bit] -> n
count bs = summ_cut 2 $ map fromBit bs


------------------------------------------------------------

test =
  -- table
  runSAT'  $ do
    xs <- replicateM 10 exists
    assert $ atmost 2 xs
    return xs


table = putStrLn $ unlines $ do
  n <- [ 1 .. 50]
  return $ unwords $ printf "n=%2d" n : do
    k <- [1..5 ]
    return $ mark (cnfsize leqSumBitsU k n)
                  (cnfsize leqSumBitsB k n)

mark x y = printf "%3d %s %3d" x (show $ compare x y) y

cnfsize f k n =
  let (_, s) = runSAT' $ do
        xs <- replicateM n exists
        assert $ f k xs
  in  -- dimacsNumVariables s - n
    -- length $ dimacsClauses s
    sum $  I.size <$> dimacsClauses s
    
