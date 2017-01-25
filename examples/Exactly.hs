{-# LANGUAGE KindSignatures #-}
-- | various implementations of the "exactly-k" constraint
-- (for arbitrary k)

{-# language Rank2Types #-}

module Exactly where

import Prelude hiding (and,or,all,any,not,(&&),(||))
import Ersatz

import Data.List (transpose)
import qualified Data.Map.Strict as M
import Control.Monad (replicateM, forM_)
import Control.Monad.State.Class

data Method = Binaries 
         | SumBits
         | SumBit
         | Chinese
         | Plain
         | QSort
  deriving Show

assert_exactly ::  (HasSAT s, Control.Monad.State.Class.MonadState s m) => Method -> Int -> [Bit] -> m ()
assert_exactly exa n xs = case exa of
  Binaries -> assert_exactly_binaries n xs
  Chinese -> assert $ exactly_chinese n xs
  SumBits -> assert $ encode (fromIntegral n) === sumBits xs
  SumBit  -> assert $ encode (fromIntegral n) === sumBit  xs
  Plain -> assert $ exactly_plain n xs
  QSort -> assert_qsort n xs

assert_qsort :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => Int -> [Bit] -> m ()
assert_qsort n xs = do
  let (lo,hi) = splitAt n $ qsort xs
  assert $ and lo
  assert $ not $ or hi

-- | http://www.iti.fh-flensburg.de/lang/algorithmen/sortieren/twodim/shear/shearsorten.htm
qsort :: forall a. Boolean a => [a] -> [a]
qsort [] = []
qsort [x] = [x]
qsort [x,y] = [ x || y , x && y ]
qsort [x,y,z] = [ x || y || z, x&&y || y&&z || z&&x  , x && y && z ]
qsort xs = take (length xs) $ 
  let w = round $ sqrt $ fromIntegral $ length xs
      k = truncate $ logBase 2 $ fromIntegral $ length xs
  in  concat $ map qsort $ iterate phase (blocks w xs) !! k

phase :: Boolean b => [[b]] -> [[b]]
phase = transpose . map qsort . transpose . zigzag . map qsort 

zigzag :: forall a. [[a]] -> [[a]]
zigzag (x:y:zs) = x : reverse y : zigzag zs
zigzag xs = xs

blocks :: forall a. Boolean a => Int -> [a] -> [[a]]
blocks w [] = []
blocks w xs = 
  let (lo,hi) = splitAt w xs 
  in  if null hi 
      then [ take w $ lo ++ repeat false ]
      else lo : blocks w hi

assert_exactly_binaries :: (HasSAT s, Control.Monad.State.Class.MonadState s m) => Int -> [Bit] -> m ()
assert_exactly_binaries n xs = do
  let w = length xs
      b = succ $ truncate $ logBase 2 $ fromIntegral $ w - 1
  ms <- replicateM n ( Bits <$> replicateM b exists )
  assert $ and $ zipWith (<?) ms $ tail ms ++ [ encode $ fromIntegral w ]
  forM_ (zip [0 :: Integer ..] xs) $ \ (k, x) -> do
    assert $ x === any (encode k ===) ms

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

exactly_plain :: forall a. Boolean a => Int -> [a] -> a
exactly_plain n xs = 
  let s = foldb (uf_plus_cut (n+1)) $ map uf_unit xs
  in  not (over s) && (contents s !! n)

atmost_plain :: forall b. Boolean b => Int -> [b] -> b
atmost_plain n xs = 
  let s = foldb (uf_plus_cut (n+1)) $ map uf_unit xs
  in  not (over s) 


-- | FIXME: broken at the moment?
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
