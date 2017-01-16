-- | see also
-- http://www.research.ibm.com/people/s/shearer/grtab.html
-- http://cube20.org/golomb/

{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}

import Prelude hiding (and,or,all,any,not,(&&),(||))
import qualified Prelude as P
import Ersatz
import Control.Monad
import Data.Monoid
import Data.List (foldl', transpose)
import System.Environment
import Data.Time
import Data.Bits (testBit)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

main :: IO ()
main = getArgs >>= \ case
  [ n, b ] -> void $ run (read n) (Just $ read b)
  [ n ] -> search $ read n
  [] -> search 8

search n = do
  let go bound = run n bound >>= \ case
        Nothing -> return ()
        Just xs -> go $ Just $ pred $ maximum xs
  go Nothing

make w = Bits <$> replicateM w exists

run = run_unary

run_unary (n ::Int) mbound = do
  print (n, mbound)
  (status, msol@(Just bs)) <- 
      solveWith minisat $ do
        let bound = maybe (n^2) id mbound
        bs :: [Bit] <- (true :) <$> replicateM bound exists
        assert $ encode (fromIntegral n) === sumBits bs
        -- assert $ exactly n bs
	-- assert $ atleast n bs
        assert $ Bits bs <? Bits (reverse bs)
        forM_ [1 .. bound] $ \ dist -> when (2*dist <= bound) $ do
          let ds = do 
                p <- [ 0..bound] ; let { q = p + dist } 
                guard $ q <= bound
                return $ and [bs !! p, bs !! q ]
          -- assert_atmost_one_squared ds
          -- assert_atmost_one_binary ds
          -- assert_atmost_one_project ds
	  assert_atmost_one_logpro ds
          -- assert $ atmost_one ds
        return bs
  case status of
    Satisfied -> do 
      let xs = do (x,True) <- zip [0..] bs ; return x
      print xs
      getCurrentTime >>= print 
      return $ Just xs
    _ -> return Nothing

assert_atmost_one_squared xs = do
  let blocks k [] = []
      blocks k xs = 
        let (here, there) = splitAt k xs
        in  here : blocks k there
  let go xs | length xs > 4 = do
         let w = round $ sqrt $ fromIntegral $ length xs
         leaders <- forM ( transpose $ blocks w xs ) $ \ block -> do
           leader <- exists
           go $ not leader : block
           return leader
         go leaders
      go xs = assert_atmost_one_binary xs
  go xs

assert_atmost_one_logpro xs = do
  let go pos = do
         let m = M.fromListWith (||) $ do
	       (k,x) <- zip [0 :: Int ..] xs
	       return (testBit k pos, x)
	 assert $ not $ and m
  if length xs > 4
    then forM_ [ 0 .. truncate $ logBase 2 $ fromIntegral $ (length xs - 1) ] go
    else assert_atmost_one_unary xs

assert_atmost_one_project xs = do
  let blocks k [] = []
      blocks k xs = 
        let (here, there) = splitAt k xs
        in  here : blocks k there
  let go xs | length xs >= 4 = do
         let w = round $ sqrt $ fromIntegral $ length xs
             m = blocks w xs
         go $ map or m 
         go $ map or $ transpose m
      go xs = assert_atmost_one_unary xs
  go xs

assert_atmost_one_unary xs = do
  forM_ (subsequences 2 xs) $ \ sub -> assert $ not $ and sub

assert_atmost_one_binary xs = do
  let w = succ $ truncate $ logBase 2 $ fromIntegral $ length xs - 1
  p <- Bits <$> replicateM w exists
  forM_ (zip [0..] xs) $ \ (k,x) -> do
    assert $ x ==> ( p === encode k )

count k xs = foldl' ( \ cs x -> zipWith (\l r -> choose l r x ) cs (false : cs) )
             (true : replicate (k-1) false) xs

atleast k xs = not $ or $ count k xs 
exactly k xs = count (k+1) xs !! k

atmost_one [] = true
atmost_one [x] = true
atmost_one xs = 
  let (lo,hi) = splitAt (div (length xs) 2) xs
  in atmost_one lo && not (or hi) || not (or lo) && atmost_one hi

{-
atmost_one xs = 
  let go [] = (true, false)
      go [x] = (not x, x)
      go xs = let (lo,hi) = splitAt (div (length xs) 2) xs
                  (lo0,lo1) = go lo ; (hi0,hi1) = go hi
              in  (lo0 && hi0 , lo0 && hi1 || lo1 && hi0)
      (zero,one) = go xs
  in  zero || one
-}

run_binary (n :: Int) mbound = do
  print (n, mbound)
  (status, msol@(Just xs)) <- 
      solveWith minisat $ do
        let w = truncate $ logBase 2 $ fromIntegral $ n^2
        xs <- replicateM n $ make w
        case mbound of
          Nothing -> return ()
          Just bound -> assert $ all (<=? encode bound) xs
        assert $ and $ zipWith (<?) xs $ tail xs
        assert $ alldifferent $ map ( \ [x,y] -> y - x ) $ subsequences 2 xs
        return xs
  case status of
    Satisfied -> do print xs ; return $ Just xs
    _ -> return Nothing

subsequences :: Int -> [a] -> [[a]]
subsequences 0 xs = [[]]
subsequences k [] = []
subsequences k (x:xs) = 
  subsequences k xs <> ( (x:) <$> subsequences (k-1) xs )

alldifferent xs = all (\ [x,y] -> x /== y ) $ subsequences 2 xs
