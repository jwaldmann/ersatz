{-# language Rank2Types #-}

module Par where

import qualified Control.Concurrent.Async as A
import Control.Monad (forM, forM_, when)
import Control.Exception (finally)

import System.IO

waitAnyCatchCancelJust :: forall a. [A.Async (Maybe a)] -> IO (Maybe a)
waitAnyCatchCancelJust [] = return Nothing
waitAnyCatchCancelJust as = do
  (a, r) <- A.waitAnyCatch as
  case r of
    Right (Just x) -> return ( Just x ) `finally` mapM_ A.cancel as
    _ -> waitAnyCatchCancelJust $ filter (/= a) as

firstJust :: [ IO (Maybe a) ] -> IO (Maybe a)
firstJust actions = do
  as <- forM actions A.async
  waitAnyCatchCancelJust as

-- | run at most the given number of processes.
-- return if any says Just.
-- List of actions could be infinite!
firstJustPool :: Int -> [ IO (Maybe a) ] -> IO (Maybe a)
firstJustPool procs actions = do
  let (now, later) = splitAt procs actions
  let go [] []  = return Nothing
      go running pending = do
         let verbose = False
         when verbose $ hPutStrLn stderr $ unwords
	    [ "running", show $ length running, "pending", show $ length pending ]
         (a,r) <- A.waitAnyCatch running
	 when verbose $ hPutStrLn stderr "caught one"
	 case r of
	   Right (Just x) -> return (Just x) `finally` forM_ running A.cancel
	   _ -> case pending of
	     [] -> go (filter (/= a) running) []
	     p : ending -> do
	         when verbose $ hPutStrLn stderr "start another"
	         b <- A.async p
		 go (b : filter (/= a) running) ending
  as <- forM now A.async
  go as later
