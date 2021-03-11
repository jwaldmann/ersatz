{-# language LambdaCase, PatternSignatures, BangPatterns #-}

import System.Environment
import Prelude hiding (and,or,not,any,all)
import Ersatz
import Ersatz.Counting
import Data.List (transpose)
import Control.Monad (replicateM)

main = getArgs >>= \ case
  [] -> mainFor 10
  [s] -> mainFor $ read s

-- | place n+1 pigeons into n holes. Unsatisfiable but hard.
mainFor n = do
  (status, _ :: Maybe ()) <- solveWith minisat $ do
    xss <- replicateM (n+1) $ replicateM n exists
    assert $ all (atleast 1) xss
    assert $ all (atmost 1) $ transpose xss
  print status
