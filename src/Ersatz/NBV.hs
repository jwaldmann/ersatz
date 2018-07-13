{-# language KindSignatures, DataKinds, TypeFamilies
  , GeneralizedNewtypeDeriving, ScopedTypeVariables, LambdaCase
  #-}

module Ersatz.NBV where

import Prelude hiding ((||),(&&),not,and,or,all,any)
import Ersatz.Bit
import Ersatz.Bits
import Ersatz.Codec
import Ersatz.Variable
import Ersatz.Equatable
import Ersatz.Orderable
import GHC.TypeLits
import Data.Proxy
import Control.Monad (replicateM)

-- | NBV = Bitvectors of fixed length, with overflow
data NBV ( n :: Nat ) = NBV { contents :: Bits, overflow :: Bit }
  deriving ( Show )

-- | FIXME: document and check: overflow is "plus infinity" in comparisons?
instance Equatable (NBV n) where
  x === y = not (overflow x) && not (overflow y) && contents x === contents y

instance Orderable (NBV n) where
  x <? y = not (overflow x) && not (overflow y) && contents x <? contents y
  x <=? y = not (overflow x) && not (overflow y) && contents x <=? contents y

instance KnownNat w => Variable (NBV w) where
  literally l = do
    let n = fromIntegral $ natVal (Proxy :: Proxy w)
    NBV <$> (Bits <$> replicateM n ( literally l )) <*> return false

positive (NBV (Bits bs) o) = or bs

nbv :: forall w . KnownNat w => Bits -> NBV w
nbv (Bits bs) =
  let n = fromIntegral $ natVal (Proxy :: Proxy w)
      (pre, post) = splitAt n bs
  in  NBV (Bits pre) $ or post

instance KnownNat n => Num (NBV n) where
  fromInteger = encode
  a + b = let c :: NBV n
              c = nbv (contents a + contents b) 
          in  c { overflow = overflow a || overflow b || overflow c }
  a * b = let c :: NBV n
              c = nbv (contents a * contents b) 
          in  c { overflow = overflow a || overflow b || overflow c }

instance KnownNat n => Codec (NBV n) where
  type Decoded (NBV n) = Integer
  decode s b = decode s (overflow b) >>= \ case 
    False -> decode s $ contents b
    True -> error "overflowed"
  encode i = nbv (encode i)
