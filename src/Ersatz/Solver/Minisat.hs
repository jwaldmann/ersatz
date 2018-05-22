--------------------------------------------------------------------
-- |
-- Copyright :  © Edward Kmett 2010-2014, Johan Kiviniemi 2013
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------

{-# language OverloadedStrings #-}

module Ersatz.Solver.Minisat
  ( minisat
  , cryptominisat
  , minisatPath
  ) where

import Data.ByteString.Builder
import Control.Exception (IOException, handle)
import Control.Monad.IO.Class
import Data.IntMap (IntMap)
import Ersatz.Problem
import Ersatz.Solution
import Ersatz.Solver.Common
import Ersatz.Solver.Stats
import qualified Data.IntMap.Strict as IntMap
import System.IO
import System.Process (readProcessWithExitCode)

import qualified Data.ByteString.Char8 as B
import Data.List ( foldl' )

-- | 'Solver' for 'SAT' problems that tries to invoke the @minisat@ executable from the @PATH@
minisat :: MonadIO m => Solver SAT m
minisat = minisatPath "minisat"

-- | 'Solver' for 'SAT' problems that tries to invoke the @cryptominisat@ executable from the @PATH@
cryptominisat :: MonadIO m => Solver SAT m
cryptominisat = minisatPath "cryptominisat"

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes @minisat@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
minisatPath :: MonadIO m => FilePath -> Solver SAT m
minisatPath path problem = liftIO $
  withTempFiles ".cnf" "" $ \problemPath solutionPath -> do
    (t_writing, ()) <- timed $ withFile problemPath WriteMode $ \fh ->
      hPutBuilder fh (dimacs problem)

    (t_solving,(exit, _out, _err)) <-
      timed $ readProcessWithExitCode path [problemPath, solutionPath] []

    (t_parsing, sol) <- timed $ parseSolutionFile solutionPath

    let stats = Stats { writing = t_writing, solving = t_solving, parsing = t_parsing
                      , variables = dimacsNumVariables problem
                      , clauses = dimacsNumClauses problem
                      }

    return (stats, (resultOf exit, sol))

parseSolutionFile :: FilePath -> IO (IntMap Bool)
parseSolutionFile path = handle handler (parseSolution <$> B.readFile path)
  where
    handler :: IOException -> IO (IntMap Bool)
    handler _ = return IntMap.empty

parseSolution :: B.ByteString -> IntMap Bool
parseSolution s =
  case B.words s of
    x : ys | x == "SAT" ->
          foldl' ( \ m y -> let Just (v,_) = B.readInt y
                            in  if 0 == v then m else IntMap.insert (abs v) (v>0) m
                 ) IntMap.empty ys
    _ -> IntMap.empty -- WRONG (should be Nothing)
