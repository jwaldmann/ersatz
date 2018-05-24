-- | various implementations of the "exactly-k" constraint
-- (for arbitrary k)

{-# language Rank2Types #-}
{-# LANGUAGE KindSignatures #-}

module Exactly where

import Prelude hiding (and,or,all,any,not,(&&),(||))
import Ersatz

import qualified AMO

import Data.List (transpose)
import qualified Data.Map.Strict as M
import Control.Monad (replicateM, forM_, when)
import Control.Monad.State.Class

data Method = Binaries 
         | SumBits
         | SumBit
         | Chinese
         | Plain
         | QSort
         | Sortnet
	 | Rectangle
  deriving Show

data Goal = Exactly |  Atmost | Atleast deriving (Eq, Ord, Show)

assert_atmost _ n xs | n < 0 = assert false
assert_atmost method n xs = case method of
  Binaries -> assert_binaries Atmost n xs
  SumBits -> assert $ encode (fromIntegral n) >=? sumBits xs
  SumBit  -> assert $ encode (fromIntegral n) >=? sumBit  xs
  Plain -> assert $ count_plain Atmost n xs
  QSort -> assert_qsort Atmost n xs
  Sortnet -> assert_sortnet Atmost n xs
  Rectangle -> assert_rectangle Atmost n xs  

assert_exactly ::  (HasSAT s, Control.Monad.State.Class.MonadState s m) => Method -> Int -> [Bit] -> m ()
assert_exactly method n xs = case method of
  Binaries -> assert_binaries Exactly n xs
  Chinese -> assert $ exactly_chinese n xs
  SumBits -> assert $ encode (fromIntegral n) === sumBits xs
  SumBit  -> assert $ encode (fromIntegral n) === sumBit  xs
  Plain -> assert $ count_plain Exactly n xs
  QSort -> assert_qsort Exactly n xs
  Sortnet -> assert_sortnet Exactly n xs

assert_rectangle Atmost n xs = do
  yss <- replicateM n $ replicateM (length xs) exists
  forM_ yss $ AMO.assert_atmost_one ( AMO.Project 8 )
  forM_ (zip xs $ transpose yss) $ \ (x,ys) -> assertClause $ not x : ys

assert_sortnet goal n xs = do
  let (lo,hi) = splitAt n $ sortnet xs
  when (goal == Atleast || goal == Exactly) 
     $ when (not $ null lo) $ assert $ last lo
  when (goal == Atmost || goal == Exactly) 
     $ when (not $ null hi) $ assert $ not $ head hi
  
sortnet xs = 
  if length xs > 1 
  then let (lo,hi) = eo xs
       in mergenet (sortnet lo) (sortnet hi)
  else xs

eo [] = ([],[])
eo (x:xs) = let (ys,zs) = eo xs in (x:zs,ys)

mergenet [] ys = ys ; mergenet xs [] = xs
mergenet [x] [y] = [ x||y , x&&y ]
mergenet xs ys = 
  let (ex,ox) = eo xs
      (ey,oy) = eo ys
      e : es = mergenet ex ey
      os = mergenet ox oy
      go (x:xs) (y:ys) = (x||y) : (x&&y) : go xs ys
      go xs ys = xs ++ ys
  in  e : go os es

assert_qsort :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => Goal -> Int -> [Bit] -> m ()
assert_qsort goal n xs = do
  let (lo,hi) = splitAt n $ qsort xs
  when (goal == Atleast || goal == Exactly) $  assert $ and lo
  when (goal == Atmost || goal == Exactly) $ assert $ not $ or hi

-- | http://www.iti.fh-flensburg.de/lang/algorithmen/sortieren/twodim/shear/shearsorten.htm
qsort :: forall a. Boolean a => [a] -> [a]
qsort [] = []
qsort [x] = [x]
qsort [x,y] = [ x || y , x && y ]
-- qsort [x,y,z] = [ x || y || z, x&&y || y&&z || z&&x  , x && y && z ]
qsort xs = 
  let w = round $ sqrt $ fromIntegral $ length xs
      -- w = 2 -- div (length xs + 1) 2
      bs = blocks w xs
      k = truncate $ logBase 2 $ fromIntegral $ length bs
  in  concat $ map qsort $ iterate phase bs !! k

phase :: Boolean b => [[b]] -> [[b]]
phase = transpose . map qsort . transpose . zigzag . map qsort 

zigzag :: forall a. [[a]] -> [[a]]
zigzag (x:y:zs) = x : reverse y : zigzag zs
zigzag xs = xs

blocks :: forall a. Boolean a => Int -> [a] -> [[a]]
blocks w [] = []
blocks w xs = 
  let (lo,hi) = splitAt w xs 
  in  lo : if null hi then [] else blocks w hi

assert_binaries :: (HasSAT s, Control.Monad.State.Class.MonadState s m) => Goal -> Int -> [Bit] -> m ()
assert_binaries goal n xs = do
  let w = length xs
      b = succ $ truncate $ logBase 2 $ fromIntegral $ w - 1
  ms <- replicateM n ( Bits <$> replicateM b exists )
  case goal of
    Exactly -> assert $ and $ zipWith (<?) ms $ tail ms ++ [ encode $ fromIntegral w ]
    Atmost -> return ()
  forM_ (zip [0 :: Integer ..] xs) $ \ (k, x) -> do
    assert $ x === any (encode k ===) ms

-- | unary representation with fixed bit width
data UF b = UF { contents :: [b] , over :: b }

uf_unit ::  Boolean b => b -> UF b
uf_unit x = UF { contents = [not x, x], over = false }

uf_plus_cut :: forall b. Boolean b => Int -> UF b -> UF b -> UF b
uf_plus_cut cut a b = 
  let res = M.toAscList $ M.fromListWith (||) $ do 
         (p,x) <- zip [0..] $ contents a
         (q,y) <- zip [0..] $ contents b
         return (p + q, x && y)
      (pre,post) = splitAt cut $ map snd res
  in  UF { contents = pre
         , over = over a || over b || or post
         }

count_plain :: forall a. Boolean a => Goal -> Int -> [a] -> a
count_plain goal n xs = 
  let s = foldb (uf_plus_cut (n+1)) $ map uf_unit xs
  in  case goal of
     Exactly -> not (over s) && (contents s !! n)
     Atmost -> not (over s)
     Atleast -> over s || (contents s !! n)

-- exactly_chinese :: forall b. (Equatable b, Boolean b) => Int -> [b] -> Bit
exactly_chinese :: forall b. (Equatable b, Boolean b) => Int -> [b] -> Bit
exactly_chinese n [] = bool (n == 0)
exactly_chinese n xs = 
  let good m = 
        let r = foldb plusmod $ map (unit m) xs
        in  r === encode_mod m n
  in  all good $ take (mods $ length xs) primes

unit :: forall a. Boolean a => Int -> a -> [a]
unit m x = not x : x : replicate (m-2) false

primes :: [Int]
primes = sieve [2..]
sieve :: forall a. Integral a => [a] -> [a]
sieve (x : ys) = x : sieve (filter (\y -> 0 /= mod y x) ys)

mods :: Int -> Int
mods n = length $ takeWhile (<= n) $ scanl (*) 1 primes

encode_mod :: forall b a. (Boolean b, Integral a) => a -> a -> [b]
encode_mod m n = 
  map ( \ i -> bool $ mod n m == i ) [0..m-1]

plusmod :: Boolean b => [b] -> [b] -> [b]
plusmod xs ys =
  let rot (y:ys) = ys ++ [y]
  in  zipWith (\ _ q -> or $ zipWith (&&) xs q) xs 
           (map reverse $ drop 1 $ iterate rot ys)

foldb :: (a -> a -> a) -> [a] -> a
foldb f [] = error "foldb []"
foldb f [x] = x
foldb f xs = 
  let (lo,hi) = splitAt (div (length xs) 2) xs
  in  f (foldb f lo) (foldb f hi)
