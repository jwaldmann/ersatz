{-# language LambdaCase #-}

module Main where

import Ersatz
import Control.Monad
import System.Environment

problem :: MonadSAT s m => Integer -> m (Bits, Bits)
problem n = do
  let w = ceiling $ logBase 2 $ fromIntegral n
  a <- liftM Bits (replicateM w exists)
  b <- liftM Bits (replicateM w exists)
  let c = a * b
  assert (a /== encode 1)
  assert (b /== encode 1)
  assert (c === encode n)
  return (a,b)

main :: IO ()
main = getArgs >>= \ case
 [] -> -- mainFor 1000000000001
   mainFor 11111111111
 [s] -> mainFor $ read s

mainFor :: Integer -> IO ()
mainFor n = do
  putStrLn "Solution:"
  (Satisfied, Just (a,b)) <-
    -- solveWith cryptominisat5 $ problem n
    solveWith minisat $ problem n
  putStrLn $ unwords
    [ "solver claims that", show n, "=", show a, "*", show b ]
  when (a * b /= n) $ error $ unwords [ "but a * b =", show (a*b) ]
