{-# language KindSignatures, DataKinds, FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TypeFamilies, ScopedTypeVariables #-}
{-# language UndecidableInstances #-}
{-# language NoMonomorphismRestriction #-}

import Prelude hiding ( not, and, or, (&&), (||) )

import Ersatz
import Ersatz.NBV

import GHC.TypeLits
import Data.Proxy
import Data.List ( transpose )
import Control.Monad ( replicateM, forM_ )
import Control.Monad.State

main = do
  (stats, (Satisfied, Just ms)) <- solveWithStats minisat $ do
    [ Restricted a, Restricted b ]
        :: [ Restricted 5 (NBV 3) ] <- replicateM 2 exists
    -- assert $ gt (a^2 * b^2) (b^3 * a^3)
    let a2 = a^2 ; b2 = b^2
    assert $ gt (a2 * b2) (b2 * b * a * a2)
    return [a,b]
  forM_ ms print
  print stats

unknown_monotone = do
   m <- exists ; assert $ monotone m ; return m

newtype Restricted d a = Restricted (Matrix d a)

instance (KnownNat dim, Variable a, Codec a, Num (Decoded a))
  => Variable (Restricted dim a) where
  literally l = do
    let d = fromIntegral $ natVal (Proxy :: Proxy dim)
        row f = ( encode f : ) <$> replicateM (d-1) (literally l)
    m <- (:) <$> row 1 <*> replicateM (d-2) (row 0)
    return $ Restricted $ Matrix
       $ m ++ encode [ replicate (d-1) 0 ++ [1] ]

-- | square matrices
newtype Matrix (dim::Nat)  a = Matrix [[a]]
  deriving ( Show, Equatable, Orderable )

instance Codec a => Codec (Matrix dim a) where
  type Decoded (Matrix dim a) = Matrix dim (Decoded a)
  decode s (Matrix xss) = Matrix <$> decode s xss

instance (KnownNat dim, Variable a) => Variable (Matrix dim a) where
  literally l = do
    let d = fromIntegral $ natVal (Proxy :: Proxy dim)
    Matrix <$> replicateM d (replicateM d $ literally l)

instance Num a => Num (Matrix dim a) where
  Matrix xss + Matrix yss
    = Matrix $ zipWith (zipWith (+)) xss yss
  Matrix xss * Matrix yss
    = Matrix $ for xss $ \ row ->
        for (transpose yss) $ \ col ->
          sum $ zipWith (*) row col

for = flip map

topleft (Matrix xss) = head (head xss)
botright (Matrix xss) = last (last xss)
topright (Matrix xss) = last (head xss)

monotone m = positive (topleft m) && positive (botright m)

ge :: Orderable a => Matrix dim a -> Matrix dim a -> Bit
ge (Matrix xss) (Matrix yss) =
  and $ zipWith (>=?) (concat xss) (concat yss)

gt :: Orderable a => Matrix dim a -> Matrix dim a -> Bit
gt a b = ge a b && topright a >? topright b

