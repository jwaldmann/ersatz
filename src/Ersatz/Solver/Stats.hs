module Ersatz.Solver.Stats where

import Data.Time.Clock

data Stats = Stats
  { writing :: NominalDiffTime
  , solving :: NominalDiffTime
  , parsing ::NominalDiffTime
  , variables :: Int
  , clauses :: Int
  } deriving Show

timed :: IO a -> IO (NominalDiffTime, a)
timed action = do
  start <- getCurrentTime
  result <- action
  end <- getCurrentTime
  return (diffUTCTime end start, result)
  
