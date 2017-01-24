-- | various implementations of the at-most-one constraint

module AMO where

import Prelude hiding (and,or,all,any,not,(&&),(||))
import qualified Prelude as P
import Ersatz

import qualified Data.Map.Strict as M
import Data.List (transpose, foldl')
import Control.Monad (forM, forM_, replicateM)
import Data.Bits

data Method = Squared Int 
         | Project Int
         | LogPro  Int
         | Unary
         | Binary
         | Plain
  deriving (Show)

assert_atmost_one alg xs = case alg of
   Squared cut -> assert_atmost_one_squared cut xs
   Project cut -> assert_atmost_one_project cut xs
   LogPro cut -> assert_atmost_one_logpro cut xs
   Unary -> assert_atmost_one_unary xs
   Binary -> assert_atmost_one_binary xs
   -- AMO_Plain -> assert $ atmost_plain 1 xs
  
assert_atmost_one_squared cut xs = do
  let blocks k [] = []
      blocks k xs = 
        let (here, there) = splitAt k xs
        in  here : blocks k there
  let go xs | length xs >= cut = do
         let w = round $ sqrt $ fromIntegral $ length xs
         leaders <- forM ( transpose $ blocks w xs ) $ \ block -> do
           leader <- exists
           go $ not leader : block
           return leader
         go leaders
      go xs = assert_atmost_one_unary xs
  go xs

assert_atmost_one_logpro cut xs = do
  let go pos = do
         let m = M.fromListWith (||) $ do
	       (k,x) <- zip [0 :: Int ..] xs
	       return (testBit k pos, x)
	 assert $ not $ and $ M.elems m
  if length xs >= cut
    then forM_ [ 0 .. truncate $ logBase 2 $ fromIntegral $ (length xs - 1) ] go
    else assert_atmost_one_unary xs

assert_atmost_one_project cut xs = do
  let blocks k [] = []
      blocks k xs = 
        let (here, there) = splitAt k xs
        in  here : blocks k there
  let go xs | length xs >= cut = do
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

subsequences :: Int -> [a] -> [[a]]
subsequences 0 xs = [[]]
subsequences k [] = []
subsequences k (x:xs) = 
  subsequences k xs ++ ( (x:) <$> subsequences (k-1) xs )

alldifferent xs = all (\ [x,y] -> x /== y ) $ subsequences 2 xs
