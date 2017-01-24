-- | see also
-- http://www.research.ibm.com/people/s/shearer/grtab.html
-- http://cube20.org/golomb/

{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}

import Prelude hiding (and,or,all,any,not,(&&),(||))
import qualified Prelude as P
import Ersatz
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
import Control.Exception (finally)
import qualified GHC.Conc
import Control.Lens ( (^.))
import Data.Foldable (toList)

main :: IO ()
main = getArgs >>= \ case
  [ n, b ] -> void $ run_best configs (read n) (Just $ read b)
  [ n ] -> search configs $ read n
  [] -> search configs 8

configs = Config 
  <$> [ SumBits  
      -- , Chinese
       ] 
  <*> ( []
      ++ [ AMO_Binary ]
     --  ++ ( [ Project , LogPro  ]  <*> [ 7, 12 ] )
      ++  (Based <$> [ 8 ] <*> [ 8 ] )
    )

search confs n = do
  let go bound = run_best confs n bound >>= \ case
        Nothing -> return ()
        Just xs -> go $ Just $ pred $ maximum xs
  go $ Just (n^2)

data Config = 
     Config { exa :: EXA
            , amo :: AMO
            } deriving Show

data Args =
    Args { _conf :: Config
         , _n :: Int
         , _mbound :: Maybe Int
         }
  deriving Show

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

        assert_exactly (exa conf) n bs

        -- different_sums conf bs
	different_differences conf bs
	-- plain_clauses bs
	-- enough_diffs conf n bs
	
        return bs
enough_diffs conf n bs = do
  assert_exactly (exa conf) (div (n * (n-1)) 2)
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
          assert_atmost_one (amo conf) ds

different_sums conf  bs = do
  let bound = length bs - 1
  forM_ [1 .. 2 * bound] $ \ s -> do
	  let ss = do
	        p <- [0 .. min s bound ] ; let q = s - p
		guard $ p <= q P.&& q <= bound
		return $ and [bs !! p, bs !! q ]
          when (not $ null ss) $ assert_atmost_one (amo conf) ss

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

-- * atmost

atmost k xs = encode (fromIntegral k) >=? sumBits xs

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
	 | Based Int Int
         | AMO_Unary
         | AMO_Binary
         | AMO_Plain
  deriving (Show)

assert_atmost_one alg xs = case alg of
   Squared cut -> assert_atmost_one_squared cut xs
   Project cut -> assert_atmost_one_project cut xs
   LogPro cut -> assert_atmost_one_logpro cut xs
   Based base cut -> assert_atmost_one_based base cut xs
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


assert_atmost_one_based base cut xs = do
  let testBit n 0 = mod n base
      testBit n pos = testBit (div n base) (pos - 1)
      go pos = do
         let m = M.fromListWith (||) $ do
	       (k,x) <- zip [0 :: Int ..] xs
	       return (testBit k pos, x)
	 assert_atmost_one_unary $ M.elems m
  if length xs >= cut
    then forM_ [ 0 .. truncate $ logBase (fromIntegral base) $ fromIntegral $ (length xs - 1) ] go
    else assert_atmost_one_unary xs

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
