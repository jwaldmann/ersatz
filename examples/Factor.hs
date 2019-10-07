{-# language LambdaCase #-}

module Main where

import Ersatz
import Control.Monad (replicateM, when)
import System.Environment (getArgs)

problem :: MonadSAT s m => Integer -> m (Bits, Bits)
problem c = do
  let Bits bs = encode c ; w = length bs
  a <- Bits <$> replicateM w exists
  b <- Bits <$> replicateM w exists
  assert (a /== encode   1)
  assert (b /== encode   1)
  assert (a * b === encode c)
  return (a,b)

main :: IO ()
main = getArgs >>= \ case
  [] -> handle $ 10^10 + 1
  [s] -> handle $ read s

handle c = do
  putStrLn $ "factorization of " ++ show c
  (Satisfied, Just (a,b)) <-
    solveWith glucose $ problem c
  putStrLn (show a ++ " * " ++ show b ++ " = " ++ show c)
  when (a * b /= c) $ error "WAT"
