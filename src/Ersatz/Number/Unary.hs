{-# language KindSignatures, DataKinds, TypeApplications, ScopedTypeVariables, RankNTypes, LambdaCase, TypeFamilies #-}

module Ersatz.Number.Unary where

import Prelude hiding (and,or,not,(||),(&&),any,all)
import Ersatz.Bit
import Ersatz.Bits (Bits(..),FromBit(..))
import Ersatz.Codec
import Ersatz.Equatable
import Ersatz.Orderable

import GHC.TypeLits
import Data.Proxy
import Data.Reflection
import Data.List (genericLength)
import Control.Monad (replicateM)

-- | Numbers with bounded bit width and overflow detection.
-- Implementation uses order encoding.
-- contents x !! k  <==> value-of x >= k.
-- For @w=3@, encodings are
-- 0 => U [1,0,0] 0, 1 => U [1,1,0] 0, 2 => U [1,1,1] 0,
-- 3 and more => U [1,1,1] 1
data Unary (w :: Nat) =
  Unary { contents :: ![Bit]
        -- ^ will have length  w, first bit is constant true
       , overflow :: !Bit
       }

instance forall w . KnownNat w => Codec (Unary w) where
  type Decoded (Unary w) = Integer
  decode s b = decode s (overflow b) >>= \ case
    False -> decode s (contents b) >>= \ (_ : bs) ->
      return $ genericLength $ takeWhile id bs
    True -> error "overflow"
  encode n =
    let w = natVal @w undefined
    in  Unary { contents = map (\k -> bool $ n >= k) [0..w-1]
              , overflow = bool (n >= w)
              }

-- | @x /== y@ is not the negation of  @x === y@.
-- an overflowed number is never equal
-- to another number (overflowed or not).
-- an overflowed number is unequal to a non-overflowed number.
instance Equatable (Unary w) where
  x === y = and (zipWith (===) (contents x) (contents y))
    && not (overflow x) && not (overflow y)
  x /== y = or (zipWith (/==) (contents x) (contents y))
    && not (overflow x) && not (overflow y)
    || (overflow x /== overflow y)

instance Orderable (Unary w) where
  x <=? y = and (zipWith (<=?) (contents x) (contents y))
    && not (overflow x) -- overflow y is accepted
  x >=? y = y <=? x  
  x <? y = or (zipWith (<?) (contents x) (contents y))
    && not (overflow x) -- overflow y is accepted
  x >? y = y <? x  

instance forall w . KnownNat w => FromBit (Unary w) where
  fromBit b =
    let w = fromIntegral $ natVal @w undefined
        bs = take (w+1) $ true : b : repeat false
    in  Unary { contents = take w bs , overflow = bs !! w }

instance forall w . KnownNat w => Num (Unary w) where
  a + b =
    let w = fromIntegral $ natVal @w undefined
        get x i = if i < w then contents x !! i else overflow x
        cs = do
          k <- [0 .. w]
          return $ or $ do
            i <- [0 .. k]
            return $ get a i && get b (k-i)
    in  Unary (take w cs) (cs !! w)

