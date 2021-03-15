{-# language LambdaCase, PatternSignatures, BangPatterns #-}

import System.Environment
import Prelude hiding (and,or,not,any,all)
import Ersatz
import Ersatz.Counting
import Data.List (transpose)
import Control.Monad (replicateM, when)

main = getArgs >>= \ case
  [] -> do
    -- mainFor   1 25
    -- mainFor   3 25
    -- mainFor  12 25
    mainFor 5 30
  [d, n] -> mainFor (read d) (read n)

-- a n-by-n matrix where
-- each row has atlest d entries true,
-- and each column has atmost d entries true.
-- it follows that the numbers are exact
-- (consider the sum over all entries)
mainFor d n = do
  (Satisfied, Just m) <- solveWith minisat $ do
    xss <- replicateM n $ replicateM n exists
    assert $ all (atleast d) $           xss
    assert $ all (atmost  d) $ transpose xss
    return xss
  let a = map (map fromEnum) m
  mapM_ print a
  when (not $ all (== d) $ map sum a) $ error "wrong row"
  when (not $ all (== d) $ map sum $ transpose a) $ error "wrong column"
