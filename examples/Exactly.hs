-- | various implementations of the "exactly-k" constraint
-- (for arbitrary k)

{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# language Rank2Types #-}

module Exactly where

import Prelude hiding (and,or,all,any,not,(&&),(||))
import Ersatz

import qualified Data.Map.Strict as M
import Control.Monad (replicateM, forM_)
import Control.Monad.State.Class

data Method = Binaries 
         | SumBits
         | Chinese
         | Plain
  deriving Show

assert_exactly ::  (HasSAT s, Control.Monad.State.Class.MonadState s m) => Method -> Int -> [Bit] -> m ()
assert_exactly exa n xs = case exa of
  Binaries -> assert_exactly_binaries n xs
  Chinese -> assert $ exactly_chinese n xs
  SumBits -> assert $ encode (fromIntegral n) === sumBits xs
  Plain -> assert $ exactly_plain n xs

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
exactly_chinese :: forall b. (Equatable b, Boolean b) => Int -> [b] -> Bit
exactly_chinese n xs = 
  let good m = 
        let r = foldb plusmod $ map (unit m) xs
        in  r === encode_mod m n
  in  all good $ take (mods n) primes

unit m x = not x : x : replicate (m-2) false

primes :: [Int]
primes = sieve [2..]
sieve :: forall a. Integral a => [a] -> [a]
sieve (x : ys) = x : sieve (filter (\y -> 0 /= mod y x) ys)

mods :: Int -> Int
mods n = length $ takeWhile (<= n) $ scanl (*) 1 primes

instance Equatable Bool where x === y = bool (x == y)

encode_mod :: forall b a. (Boolean b, Integral a) => a -> a -> [b]
encode_mod m n = 
  map ( \ i -> bool $ mod n m == i ) [0..m-1]

plusmod :: Boolean b => [b] -> [b] -> [b]
plusmod xs ys =
  let rot (y:ys) = ys ++ [y]
  in  zipWith (\ _ q -> or $ zipWith (&&) xs q) xs 
           (map reverse $ drop 1 $ iterate rot ys)

foldb :: (a -> a -> a) -> [a] -> a
foldb f [x] = x
foldb f xs = 
  let (lo,hi) = splitAt (div (length xs) 2) xs
  in  f (foldb f lo) (foldb f hi)
