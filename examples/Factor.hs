{-# language LambdaCase, TypeApplications, PatternSignatures, KindSignatures, DataKinds, AllowAmbiguousTypes #-}

module Main where

import Ersatz
import Ersatz.Number.Binary
import Control.Monad
import System.Environment
import Data.Reflection
import Data.Proxy
import Data.Kind
import GHC.TypeLits

problem
  :: forall (w ::Nat) s m
  . (KnownNat w, MonadSAT s m)
  => Integer
  -> m (Binary w, Binary w)
  --  -> m (Bits, Bits)
problem n = do
  a :: Binary w <- exists
  b <- exists
  -- let w = fromIntegral $ natVal @w undefined
  -- a <- Bits <$> replicateM w exists
  -- b <- Bits <$> replicateM w exists
  let c = a * b
  assert (a /== encode 1)
  assert (b /== encode 1)
  assert (c === encode n)
  return (a,b)

main :: IO ()
main = getArgs >>= \ case
 [] -> do
   mainFor 1000000000001
   -- Bits: variables: 9457 clauses: 33485
   -- Binary: variables: 6455 clauses: 25156
   mainFor 11111111111
   -- Bits: variables: 6811 clauses: 24163
   -- Binary: variables: 4629 clauses: 18030
 [s] -> mainFor $ read s

mainFor :: Integer -> IO ()
mainFor n = do
  putStrLn "Solution:"
  let w = ceiling $ logBase 2 $ fromIntegral n
  reifyNat w $ \ (_ :: Proxy w) -> do
      (Satisfied, Just (a,b)) <-
        -- solveWith cryptominisat5 $ problem n
        solveWith minisat $ problem @w n
      putStrLn $ unwords
        [ "solver claims that", show n, "=", show a, "*", show b ]
      when (a * b /= n)
        $ error $ unwords [ "but a * b =", show (a*b) ]
