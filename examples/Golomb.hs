-- | see also
-- http://www.research.ibm.com/people/s/shearer/grtab.html
-- http://cube20.org/golomb/

{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}

import Prelude hiding (and,or,all,any,not,(&&),(||))
import qualified Prelude as P
import Ersatz

import qualified Exactly as E
import qualified AMO as AMO
import Par

import Ersatz.Internal.Formula (formulaSet)
import Control.Monad
import Data.Monoid
import Data.List (foldl', transpose, tails, cycle, sortOn)
import System.Environment
import System.IO
import Data.Time
import Data.Bits (testBit)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Q
import qualified Control.Concurrent.Async as A
import qualified GHC.Conc
import Control.Lens ( (^.))
import Data.Foldable (toList)

main :: IO ()
main = getArgs >>= \ case
  [ n, b ] -> void $ run_best configs (read n) (Just $ read b)
  [ n ] -> search configs $ read n
  [] -> search configs 8

configs = Config 
  <$> [  E.SumBits  , 
       E.Chinese ] 
  <*> ( [ --  Squared  , 
          AMO.Project , AMO.LogPro  ] 
       <*> [  5, 6, 9, 12 ] ) 

search confs n = do
  let go bound = run_best confs n bound >>= \ case
        Nothing -> return ()
        Just xs -> go $ Just $ pred $ maximum xs
  go $ Just (n^2)

data Config = 
     Config { exa :: E.Method
            , amo :: AMO.Method
            } deriving Show

data Args =
    Args { _conf :: Config
         , _n :: Int
         , _mbound :: Maybe Int
         }
  deriving Show

run_best confs n mbound = do
  putStrLn $ unwords [ "run_best for", show n, show mbound, "with", show (length confs), "configuration candidates" ]
  let args = sortOn fst $ do
        conf <- confs
        let arg = Args { _conf = conf, _n = n, _mbound = mbound } 
        return (clauses $ constraint arg, arg)
  numcaps <- GHC.Conc.getNumCapabilities
  putStrLn "formula sizes per config"
  mapM_ print $ reverse $ zip [1..] $ take (2*numcaps) args
  putStrLn "start actual computation for top half of previous list"
  firstJust $ map run $ take numcaps $ map snd args 
  
run arg = do
  print arg
  (stats,(status, msol@(Just bs))) <- 
      solveWithStats minisat $ constraint arg
  print (arg,stats)
  case status of
    Satisfied -> do 
      let xs = do (x,True) <- zip [0..] bs ; return x
      print xs
      getCurrentTime >>= print  ; hFlush stdout
      return $ Just xs
    _ -> return Nothing

clauses con =
  let (_,f) = runSAT' con
  in  Q.length $ formulaSet ( f ^. formula )

constraint arg = do
        let conf = _conf arg
            n = _n arg
            mbound = _mbound arg
            bound = maybe (n^2) id mbound
        bs :: [Bit] <- (true :) <$> replicateM bound exists
        -- blockchain n bs
	-- blockchain n $ reverse bs

        E.assert_exactly (exa conf) n bs

        -- different_sums conf bs
	different_differences conf bs
	-- plain_clauses bs
	-- enough_diffs conf n bs
	
        return bs

enough_diffs conf n bs = do
  E.assert_exactly (exa conf) (div (n * (n-1)) 2)
     $ toList $ M.fromListWith (||) $ do
         (x:ys) <- tails bs
	 (d,y) <- zip [1 ..] ys
	 return (d, x && y)

plain_clauses bs = do
  let top = length bs - 1
  forM_ [1.. top] $ \ dist ->
    forM_ [0 .. top-dist] $ \ i ->
       forM_ [i + dist .. top-dist] $ \ j ->
         assertClause $ map not $ map (bs !!) [  i, i+dist, j, j+dist ]


different_differences conf bs = do
  let bound = length bs - 1
  forM_ [1 .. bound] $ \ dist -> when (2*dist <= bound) $ do
          let ds = do 
                p <- [ 0..bound] ; let { q = p + dist } 
                guard $ q <= bound
                return $ and [bs !! p, bs !! q ]
          AMO.assert_atmost_one (amo conf) ds

different_sums conf  bs = do
  let bound = length bs - 1
  forM_ [1 .. 2 * bound] $ \ s -> do
	  let ss = do
	        p <- [0 .. min s bound ] ; let q = s - p
		guard $ p <= q P.&& q <= bound
		return $ and [bs !! p, bs !! q ]
          when (not $ null ss) $ AMO.assert_atmost_one (amo conf) ss

blockchain n bs = do
  let go d prev bs =
        if d < n
	then do
	  let (pre, post) = splitAt d bs
	  let s = prev + sumBits pre
	  assert $ s <=? encode (fromIntegral d)
          go (d+1) s post
	else do
	  let s = prev + sumBits bs
	  assert $ s === encode (fromIntegral n)
	  return ()
  go 1 (encode 0) bs


