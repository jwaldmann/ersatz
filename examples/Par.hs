{-# language Rank2Types #-}

module Par where

import qualified Control.Concurrent.Async as A
import Control.Monad (forM)
import Control.Exception (finally)

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

