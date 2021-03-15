{-# language KindSignatures, DataKinds, TypeApplications, ScopedTypeVariables, RankNTypes, LambdaCase, TypeFamilies #-}

module Ersatz.Number.Unary where

import Prelude hiding (and,or,not,(||),(&&),any,all)
import Ersatz.Bit
import Ersatz.Bits (Bits(..))
import Ersatz.Number.Class
import Ersatz.Codec
import Ersatz.Equatable
import Ersatz.Orderable

import GHC.TypeLits
import Data.Proxy
import Data.Reflection
import Data.List (genericLength)
import Control.Monad (replicateM)
import qualified Data.Map as M

import Debug.Trace

-- | Numbers with bounded bit width and overflow detection.
-- Implementation uses order encoding.
-- contents x !! k  <==> value-of x >= k.
-- For @w=3@, encodings are
-- 0 => U [1,0,0] 0, 1 => U [1,1,0] 0, 2 => U [1,1,1] 0,
-- 3 and more => U [1,1,1] 1.
-- @Unary w@ can represent numbers 0 .. w-1 exactly.
data Unary (w :: Nat) =
  Unary { contents :: ![Bit]
        -- ^ will have length  w, first bit is constant true
       , overflow :: !Bit
       }

contow x = contents x <> [ overflow x ]

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
        bs = true : b : repeat false
    in  Unary { contents = take w bs , overflow = bs !! w }

instance forall w . KnownNat w => Num (Unary w) where
  fromInteger 0 = fromBit false
  a + b = plus_flat @w [a,b]
          -- plus_merge @w a b

instance forall w . KnownNat w => Summ (Unary w) where
  -- summ = plus_flat

plus_merge 
  :: forall w
  . KnownNat w
  => Unary w -> Unary w -> Unary w
plus_merge x y =
  let w = fromIntegral $ natVal @w undefined
      xs = contow x ; ys = contow y
      o = or $ zipWith (&&) xs $ reverse ys
      bs = true : go (drop 1 xs) (drop 1 ys)
  in  Unary { contents = take w bs, overflow = o }

chop [] = ([],[])
chop (x:xs) = let (ys,zs) = chop xs in (x:zs,ys)

unchop [] [] = [] ; unchop [x] [] = [x]
unchop (x:xs) (y:ys) = (x||y) : (x&&y) : unchop xs ys

go [] [] = []
go [x] [y] = unchop [x] [y]
go xs ys | length xs >= 2, length ys >= 2 =
  let -- ceil(x/2), floor (x/2)
      (xe,xo) = chop xs
      -- ceil(y/2), floor (y/2)
      (ye,yo) = chop ys
      -- 1 : (ceil(x/2)+ceil(y/2)-1)
      e:es = go xe ye
      -- floor(x/2)+floor(y/2)
      os = go xo yo
  in  -- 1 + (ceil(x/2)+ceil(y/2)-1) + floor(x/2)+floor(y/2)
      -- = 1 + x + y - 1
      e : unchop os es
go xs ys =
  error $ unwords [ "go", show (length xs),show (length ys)]

plus_flat
  :: forall w
  . KnownNat w
  => [Unary w] -> Unary w
plus_flat xs =  
    let w = fromIntegral $ natVal @w undefined
        get x i = if i < w then contents x !! i else overflow x
        cs = do
          s <- [0 .. w]
          return $ or $ do
            ks <- decomp s $ length xs
            return $ and $ do
              (k,x) <- zip ks xs
              return $ get x k
    in  Unary (take w cs) (cs !! w)

-- | represent w as sum of exactly  n  non-negative numbers
decomp :: Int -> Int -> [[Int]]
decomp w 1 = return [w]
decomp 0 n = return $ replicate n 0
decomp w n = do
  k <- [0 .. w]
  (k:) <$> decomp (w-k) (n-1)
