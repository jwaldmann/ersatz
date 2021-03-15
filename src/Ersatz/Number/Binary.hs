{-# language KindSignatures, DataKinds, TypeApplications, ScopedTypeVariables, RankNTypes, LambdaCase, TypeFamilies #-}

module Ersatz.Number.Binary where

import Prelude hiding (any,all,and,or,not,(||),(&&))
import Ersatz.Bit
import Ersatz.Bits (Bits(..),sumBits)
import Ersatz.Number.Class
import Ersatz.Codec
import Ersatz.Variable
import Ersatz.Equatable
import Ersatz.Orderable

import GHC.TypeLits
import Data.Proxy
import Data.Reflection
import Data.List (genericLength)
import Control.Monad (replicateM)
import qualified Data.Map as M
import qualified Data.Sequence as Q

import Debug.Trace

-- | Numbers with bounded bit width and overflow detection.
-- Semantics for arithmetical operations
-- (currently, only addition is implemented)
-- if no overflow, then contents is correct.
-- if overflow, then contents is arbitrary.
-- Application: for bit width 1, the (only) contents bit
-- of the sum is the Or (instead of the Xor) of inputs.
-- This should help propagation in the at-most-one constraint.
data Binary (w :: Nat) =
  Binary { contents :: ![Bit] -- ^ will have length <= w
       , overflow :: !Bit
       }

instance KnownNat w => Codec (Binary w) where
  type Decoded (Binary w) = Integer
  decode s b = decode s (overflow b) >>= \ case
    False -> decode s (Bits $ contents b)
    True -> error "overflow"
  encode n = fromBits $ encode n

instance KnownNat w => Variable (Binary w) where
  literally lit =
    let w = fromIntegral $ natVal @w undefined
    in  Binary <$> (replicateM w exists) <*> pure false

-- | @x /== y@ is not the negation of  @x === y@.
-- an overflowed number is never equal
-- to another number (overflowed or not).
-- an overflowed number is unequal to a non-overflowed number.
instance Equatable (Binary w) where
  x === y = Bits (contents x) === Bits (contents y)
    && not (overflow x) && not (overflow y)
  x /== y = Bits (contents x) /== Bits (contents y)
    && not (overflow x) && not (overflow y)
    || (overflow x /== overflow y)

instance Orderable (Binary w) where
  x <=? y = Bits (contents x) <=? Bits (contents y)
    && not (overflow x) -- overflow y is accepted
  x >=? y = y <=? x  
  x <? y = Bits (contents x) <? Bits (contents y)
    && not (overflow x) -- overflow y is accepted
  x >? y = y <? x  

instance forall w . KnownNat w => FromBit (Binary w) where
  fromBit b = fromBits (Bits [b])

fromBits :: forall w . KnownNat w => Bits -> (Binary w) 
fromBits (Bits bs) =
    let w = fromIntegral $ natVal @w undefined
        (small, large) = splitAt w bs
    in  Binary { contents = small
           , overflow = or large
           }

instance forall w . KnownNat w => Summ (Binary w)

instance forall w . KnownNat w => Num (Binary w) where
  fromInteger 0 = fromBit false
  a + b =
    let w = fromIntegral $ natVal @w undefined
    in  if w == 1
        then let ha = head $ contents a <> [false]
                 hb = head $ contents b <> [false]
             in Binary { contents = [ ha || hb ]
                     , overflow =
                       overflow a || overflow b || (ha && hb)
                     }
        else
          let c = fromBits @w
               $ (Bits $ contents a) + (Bits $ contents b)
          in  c { overflow =
                  overflow a || overflow b || overflow c
                }
  a * b = 
    let w = fromIntegral $ natVal @w undefined
        c = multiply w (contents a) (contents b)
        o = if length c <= w then false else c !! w
        iszero x = all not $ contents x
    in  Binary { contents = take w c
               , overflow = not (iszero a && iszero b)
                     &&  ( overflow a || overflow b || o )
               }

-- | compute binary representation of product,
-- where bits at positions 0 .. w-1 are exact,
-- and position w indicates overflow
multiply w xs ys = reduce w $ M.fromListWith (<>) $ do
  (i,x) <- zip [0..] xs
  (j,y) <- zip [0..] ys
  return (min w $ i+j, Q.singleton (x&&y))

reduce
  :: (Ord n, Enum n, Num n)
  => n -> M.Map n (Q.Seq Bit) -> [Bit]
reduce w m = case M.minViewWithKey m of
  Nothing -> []
  Just ((k,s), m') ->
    if k < w
    then
      let Bits (b:bs) = sumBits s
          cs = M.fromList
            $ zip [k+1 .. w]
            $ map Q.singleton bs
      in  b : reduce w (M.unionWith (<>) m' cs)
    else [ or $ map or $ M.elems m ]
