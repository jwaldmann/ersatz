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
import Data.List (foldl', transpose, tails, cycle)
import System.Environment
import System.IO
import Data.Time
import Data.Bits (testBit)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Control.Concurrent.Async as A
import Control.Exception (finally)

main :: IO ()
main = getArgs >>= \ case
  [ n, b ] -> void $ run_best configs (read n) (Just $ read b)
  [ n ] -> search configs $ read n
  [] -> search configs 8

configs = Config 
  <$> [ -- Binaries , 
        SumBits 
      ] 
  <*> ( [ Squared, Project, LogPro] <*> [ 4, 8 ] )

search confs n = do
  let go bound = run_best confs n bound >>= \ case
        Nothing -> return ()
        Just xs -> go $ Just $ pred $ maximum xs
  go Nothing

data Config = 
     Config { exa :: EXA
            , amo :: AMO 
            } deriving Show

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

run_best confs n mbound = 
  firstJust $ map ( \ conf -> run conf n mbound ) confs
  
run conf (n ::Int) mbound = do
  print (n, mbound, conf)
  (stats,(status, msol@(Just bs))) <- 
      solveWithStats minisat $ do
        let bound = maybe (n^2) id mbound
        bs :: [Bit] <- (true :) <$> replicateM bound exists
        assert_exactly (exa conf) (n-1) $ tail bs
        forM_ [1 .. bound] $ \ dist -> when (2*dist <= bound) $ do
          let ds = do 
                p <- [ 0..bound] ; let { q = p + dist } 
                guard $ q <= bound
                return $ and [bs !! p, bs !! q ]
          assert_atmost_one (amo conf) ds
        return bs
  print (conf,stats)
  case status of
    Satisfied -> do 
      let xs = do (x,True) <- zip [0..] bs ; return x
      print xs
      getCurrentTime >>= print  ; hFlush stdout
      return $ Just xs
    _ -> return Nothing

-- * exactly

data EXA = Binaries 
         | SumBits
         | Chinese
         | EXA_Plain
  deriving Show

assert_exactly exa n xs = case exa of
  Binaries -> assert_exactly_binaries n xs
  Chinese -> assert $ exactly_chinese n xs
  SumBits -> assert $ encode (fromIntegral n) === sumBits xs
  EXA_Plain -> assert $ exactly_plain n xs

assert_exactly_binaries n xs = do
  let w = length xs
      b = succ $ truncate $ logBase 2 $ fromIntegral $ w - 1
  ms <- replicateM n ( Bits <$> replicateM b exists )
  assert $ and $ zipWith (<?) ms $ tail ms ++ [ encode $ fromIntegral w ]
  forM_ (zip [0 :: Integer ..] xs) $ \ (k, x) -> do
    assert $ x === any (encode k ===) ms

data UF b = UF { contents :: [b] , over :: b }

uf_unit x = UF { contents = [not x, x], over = false }

uf_plus_cut cut a b = 
  let res = M.toAscList $ M.fromListWith (||) $ do 
         (p,x) <- zip [0..] $ contents a
         (q,y) <- zip [0..] $ contents b
         return (p + q, x && y)
      (pre,post) = splitAt cut $ map snd res
  in  UF { contents = pre
         , over = over a || over b || or post
         }

exactly_plain n xs = 
  let s = foldb (uf_plus_cut (n+1)) $ map uf_unit xs
  in  not (over s) && (contents s !! n)

atmost_plain n xs = 
  let s = foldb (uf_plus_cut (n+1)) $ map uf_unit xs
  in  not (over s) 

exactly_chinese n xs = 
  let good m = 
        let unit x = not x : x : replicate (m-2) false
            r = foldb plusmod $ map unit xs
        in  r === encode_mod m n
  in  all good $ take (mods n) primes

primes = sieve [2..]
sieve (x : ys) = x : sieve (filter (\y -> 0 /= mod y x) ys)

mods n = length $ takeWhile (< n) $ scanl (*) 1 primes

instance Equatable Bool where x === y = bool (x == y)

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

-- * at most one

data AMO = Squared Int 
         | Project Int
         | LogPro  Int
         | AMO_Unary
         | AMO_Binary
         | AMO_Plain
  deriving (Show)

assert_atmost_one alg xs = case alg of
   Squared cut -> assert_atmost_one_squared cut xs
   Project cut -> assert_atmost_one_project cut xs
   LogPro cut -> assert_atmost_one_logpro cut xs
   AMO_Unary -> assert_atmost_one_unary xs
   AMO_Binary -> assert_atmost_one_binary xs
   AMO_Plain -> assert $ atmost_plain 1 xs
  
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
      go xs = assert_atmost_one_binary xs
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
  subsequences k xs <> ( (x:) <$> subsequences (k-1) xs )

alldifferent xs = all (\ [x,y] -> x /== y ) $ subsequences 2 xs
