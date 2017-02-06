-- | (minimal) dominating set on the knight's graph,
-- cf. http://oeis.org/A006075 (values for board size up to 20)
-- http://www.contestcen.com/knight.htm - larger boards:
-- 10 15 20  25   30   35   40   45   50
-- 16 36 62  96  135  182  230  291  350

{-# LANGUAGE FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language NoMonomorphismRestriction #-}
{-# language KindSignatures #-}
{-# language ExplicitForAll #-}

import Prelude hiding (and,or,not,(&&),(||),any,all)
import qualified Prelude as P
import qualified Data.Bool as P
import Ersatz

import Exactly
import qualified Par

import Control.Monad
import Control.Monad.State
import System.Environment
import Data.Foldable (toList)
import Data.List (transpose, sortOn)
import GHC.Conc
import qualified Control.Concurrent.Async as A
import qualified Data.Array as A
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Foldable (toList)
import Control.Concurrent.STM
import System.IO
import System.Random
import System.Timeout

main :: IO ()
main = do
  hSetBuffering stderr LineBuffering
  getArgs >>= \ case
    [ "local", n ] -> void $ anneal 1 (read n)
    [ "local", n, w ] -> void $ anneal (read w) (read n)
    [ "global", w, s ] -> void $ run methods (read w) (read s)
    [ "global", w] -> search methods (read w)

methods :: [Method]
methods = -- Binaries :
          SumBits :
          -- SumBit :
	  -- Rectangle :
          -- Chinese :
          -- QSort :
	  Sortnet :
          -- Plain :
          []


search :: [Method] -> Int -> IO ()
search how w = do
  let go :: Int -> IO ()
      go s = do
        out <- run how w s
        case out of
          Nothing -> return ()
          Just xss -> go $ pred $ sum $ concat xss
  go $ w^2

run :: [Method] -> Int -> Int -> IO (Maybe [[Int]])
run methods w s = do
  as <- forM methods $ \ how -> A.async $ single how w s
  (_, r) <- A.waitAnyCancel as
  return r

single :: Method -> Int -> Int -> IO (Maybe [[Int]])
single how w s = do
    print (how, w, s)
    (stats, ~(result, msol@(Just b))) <- solveWithStats minisat
        $ problem how w s
    print (how, stats)
    case result of
      Satisfied -> do
        let xss = map (map fromEnum) b
        present "original" s xss 
        let yss = map (map fromEnum) $ reduce b
        when (xss /= yss) $ present "*********** reduced" s yss 
        return $ Just yss
      _ -> do
        print result
        return Nothing

present :: forall a (t :: * -> *). (Foldable t, Show a, Num a, Eq a, Enum a) => String -> Int -> t [a] -> IO ()
present msg s xss = do
    putStrLn msg
    let form = unwords . map (\ case 0 -> "."; 1-> "K") 
    mapM_ (putStrLn . form) xss
    let c = sum $ map fromEnum $ concat xss
    putStrLn $ "actual number of knights is: " ++ show c
    when (c > s) $ error $ "what - " ++ show (sum $ concat xss)

inside a p = do
  let ((uu,ll),(oo,rr)) = A.bounds a
      ((u,l),(o,r)) = A.bounds p
  x <- [if u == uu then u else u+2 .. if o==oo then o else o-2 ]
  y <- [if l == ll then l else l+2 .. if r==rr then r else r-2 ]
  guard $ a A.! (x,y)
  return (x,y)


pick [] = error "pick []"
pick xs = (xs !!) <$> randomRIO (0,length xs-1)

biased_pick [] = error "biased_pick []"
biased_pick [x] = return x
biased_pick (x:xs) = do
  f<- randomRIO (0,1::Int)
  if f == 0 then return x else biased_pick xs

instance (Random a, Random b) => Random (a,b) where
  randomRIO ((u,l),(o,r)) = 
    (,) <$> randomRIO (u,o) <*> randomRIO (l,r)


add_randoms log k a = do
  ps <- replicateM k $ randomRIO $ A.bounds a
  unmark_all log ps
  return $ a A.// zip ps (repeat True)

anneal w n = do
  let a = A.listArray ((1,1),(n,n)) $ repeat True
  log <- atomically $ newTVar M.empty
  improve log w a 

improve log w a0 = do
  let a = -- reduca
          a0
  -- display ( show w ) a Nothing
  out <- Par.firstJustPool GHC.Conc.numCapabilities $ do
    to <- (^2) <$> [ 1 :: Int .. ]
    return $ do
      v <- return w  --  randomRIO (max 1 $ w - 1, w + 1)
      -- hPutStrLn stderr $ unwords ["start", "w", show v, "to", show to ]
      A.race (threadDelay $ to * 10^6) ( improve_step log v a ) >>= \ case
        Left {} -> return Nothing
	Right res -> return res
  case out of
     Just (v, b) -> do
       display ( show w ) b Nothing
       b <- add_randoms log (knights a - knights b) b
       improve log v b 
     Nothing -> do
       a <- add_randoms log w a
       improve log (w+1) a 

knights a = length $ filter id $ A.elems a

improve_step log w a = do
  let verbose = False
  m <- atomically $ readTVar log
  let candidates = M.fromListWith S.union
       $ map ( \ (off, bp) -> (length $ filter id $ A.elems off, S.singleton (off, bp)))
       $ filter ( \ (off,bp) -> not $ null off )
       $ filter ( \ (off, bp) -> not $ M.member (A.bounds bp) m )
       $ bordered_patches w a
  if null candidates
     then improve_step log (w+1) a
     else do
       --  print $ map (\(k,v) -> (fromIntegral k / fromIntegral (w^2) :: Double, length v)  ) $ M.toList candidates
       (inner, bp) <- biased_pick (M.toDescList candidates) >>= \ (k,v) -> pick $ toList v
       let off = map fst $ filter snd $ A.assocs inner
       	   s = length off
       when verbose $ display ("improve ..." ++ show w) a $ Just $ A.bounds bp
       mq <- local Sortnet (s - 1) (A.bounds inner) bp 
       case mq of
         Nothing -> do
           mark log (A.bounds bp)
           return Nothing
	   improve_step log (w+1) a
         Just q -> do
           let on = map fst $ filter snd $ A.assocs q
      	   let c = a A.// zip off (repeat False) A.// zip on (repeat True)
      	   when verbose $ display " ... improved" c $ Just $ A.bounds q
      	   unmark_all log $ off ++ on
      	   return $ Just (w, c)

mark log bnd = atomically $ do
  m <- readTVar log
  writeTVar log $! M.insert bnd () m

unmark_all log points = atomically $ do
  m <- readTVar log
  writeTVar log $! foldl ( \ m p -> M.filterWithKey (\bnd _ -> not $ A.inRange bnd p) m ) m points

bordered_patches w a = do
  ul@(u,l) <- A.indices a
  let or@(o,r) = (u+w-1,l+w-1)
  guard $ A.inRange (A.bounds a) or
  let inner = (ul,or)
  let inner_array = A.array inner $ do
         k <- A.range inner
         return (k, at a k)
      inner_knights = map fst $ filter snd $ A.assocs inner_array
  let a_without_inner = a A.// zip inner_knights (repeat False)
  let outer = ((u-2,l-2),(o+2,r+2))
  return (inner_array, A.array outer $ do
    p <- A.range outer
    let is_covered = not (A.inRange (A.bounds a) p)
                 || P.any (at a_without_inner) (closed_neighbours p)
    return (p, is_covered) )

-- | a set that dominates the False cells of  a,
-- and has at most  s  elements.
local :: Method
      -> Int
      -> ((Int,Int),(Int,Int))
      -> A.Array (Int,Int) Bool
      -> IO (Maybe (A.Array (Int,Int) Bool))
local how s bnd a = do
  let verbose = False
  when False $ do
    hPutStrLn stderr $ unwords ["local", show how, show s, show bnd , show $ A.bounds a ]
    display "local" a (Just bnd)
  (status, Just result) <- solveWith minisat $ do
    u <- A.listArray bnd
        <$> replicateM (A.rangeSize bnd) exists
    assert_atmost how s $ A.elems u
    forM_ (A.assocs a) $ \ (p,x) -> 
      when (not x) $ assertClause $ map ( \ q -> at u q ) $ closed_neighbours p
    return u
  case status of
    Satisfied -> return $ Just result
    _ -> return Nothing
  
info a = show (length $ filter id $ A.elems a)

wrapped i xs = [i] ++ xs ++ [i]

display msg a mp = putStrLn $ unlines $ (msg :) $ wrapped (info a ) $ do
  let ((u,l),(o,r)) = A.bounds a
  x <- [ u .. o ]
  return $ unwords $ do
    y <- [ l .. r ]
    let f = case mp of
           Just p -> A.inRange p (x,y)
           Nothing -> False
    return $ case (a A.! (x,y), f) of
      (True, False) -> "K"
      (True, True ) -> "K"
      (False, False) -> "."
      (False, True)  -> "*"


-- | dominating set of  s  knights on  w*w  board
problem :: (MonadState s m, HasSAT s)
  => Method -> Int -> Int 
  -> m [[Bit]]
problem how w s = do
  b <- allocate w 
  when False $ break_symmetries 
        [  transpose, reverse, map reverse 
        -- transpose . reverse, reverse . map reverse
        ] b
  when True $ assert_symmetries (  transpose . reverse :
                     -- reverse . map reverse :
                     --  map reverse :
		     -- transpose :
		     -- reverse :
		     []
		    )  b

  -- assert_atmost how s $ concat b
  let q = div s 4
  forM_ (quads b) $ \ yss -> assert_atmost how q $ concat yss

  -- assert_atmost how s $ concat $ transpose b
  
  let onboard (x,y) = 0 <= x P.&& x < w P.&& 0 <= y P.&& y < w
      get (x,y) = if onboard (x,y) then b !! x !! y else false
      positions = (,) <$> [0..w-1] <*> [0..w-1]
  forM_ positions $ \ p ->
    assertClause $ get p : map get (neighbours p)
  return b

quads xss = do
  let halves xs = splitAt (div (length xs) 2) xs
      front = fst . halves
      back  = snd . halves
  f <- [front, back] ; g <- [front, back]
  return $ map f $ g xss

distances :: [(Int,Int)]
distances = do
  (dx,dy) <- (,) <$> [-2..2] <*> [-2..2]
  guard $ dx^2 + dy^2 == 5
  return (dx,dy)

neighbours :: (Int, Int) -> [(Int, Int)]
neighbours (x,y) = do
  (dx,dy) <- distances
  return (x+dx,y+dy)
  
allocate :: forall (m :: * -> *) a s. (Variable a, HasSAT s, MonadState s m) => Int -> m [[a]]
allocate w = replicateM w $ replicateM w exists

assert_symmetries :: forall (t :: * -> *) (m :: * -> *) s (t1 :: * -> *) (t2 :: * -> *). (HasSAT s, MonadState s m, Foldable t2, Foldable t1, Foldable t) => t (t1 [Bit] -> t2 [Bit]) -> t1 [Bit] -> m ()
assert_symmetries ops b = do
  forM_ ops $ \ op -> 
    assert $ Bits (concat b) === Bits (concat $ op b)

break_symmetries :: forall (t :: * -> *) (m :: * -> *) s (t1 :: * -> *) a (t2 :: * -> *). (Orderable a, HasSAT s, MonadState s m, Foldable t2, Foldable t1, Foldable t) => t (t1 [a] -> t2 [a]) -> t1 [a] -> m ()
break_symmetries ops b = do
  forM_ ops $ \ op -> 
    assert $ concat b <=? concat (op b)

-- * try to reduce a solution

dominated :: A.Array (Int, Int) Bool -> Bool
dominated a = P.and $ do
  p <- A.indices a
  return $ P.or $ do
    q <- p : neighbours p
    return $ at a q

at a q = if A.inRange (A.bounds a) q then a A.! q else bool False

closed_neighbours :: (Int, Int) -> [(Int, Int)]
closed_neighbours p = p : neighbours p

reduce :: forall (t :: * -> *). Foldable t => t [Bool] -> [[Bool]]
reduce xss = 
  let w = length xss
      out = reduca $ A.listArray ((1,1),(w,w)) $ concat xss      
  in  map (\x-> map (\y -> out A.!(x,y)) [1..w]) [1..w]

reduca a =
  let next a = do
        (p,True) <- A.assocs a
        let b = a A.// [(p,False)]
        guard $ and $ (P.any (at b) $ neighbours p) : do 
           q <- neighbours p
           guard $ A.inRange (A.bounds b) q
           return $ P.any (at b) $ closed_neighbours q
        return b
      go a = case next a of
         [] -> a
         b:_ -> go b
   in go a

-- * low-level binary arithmetics (with redundant clauses)

sumBitsM :: (Foldable t, HasBits a, MonadState s m, HasSAT s)
         => t a -> m Bits
sumBitsM = sumBits'M . map bits . toList 

sumBits'M :: (  MonadState s m, HasSAT s)
         => [Bits] -> m Bits
sumBits'M [] = return $ Bits []
sumBits'M [n] = return $ Bits $ unbits n
sumBits'M ns = do
  let go (x:y:zs) = 
        (:) <$> addBitsM false x y <*> go zs
      go xs = return xs      
  sumBits'M =<< go ns    
        
addBitsM :: (  MonadState s m, HasSAT s)
         => Bit -> Bits -> Bits -> m Bits
addBitsM cin x y = do
  let add1 cin [] = return [cin]
      add1 cin (x:xs) = do
        (r,cout) <- halfAddM cin x
        rs <- add1 cout xs
        return $ r:rs
      add2 cin [] ys = add1 cin ys
      add2 cin xs [] = add1 cin xs
      add2 cin (x:xs) (y:ys) = do
        (r,cout) <- fullAddM cin x y
        rs <- add2 cout xs ys
        return $ r:rs
  Bits <$> add2 false (unbits x) (unbits y)

unbits :: Bits -> [Bit]
unbits (Bits xs) = xs

halfAddM :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => Bit -> Bit -> m (Bit, Bit)
halfAddM x y = do
  r <- fuN (\ [x, y] -> x /= y ) [x,y]
  c <- exists
  assert_implies [ x, y] [ c ]
  assert_implies [ not c] [not x]
  assert_implies [ not c] [not y]
  -- redundant, but necessary for forcing:
  when True $ do
    assert_implies [ not r, not c ] [ not x ]
    assert_implies [ not r, not c ] [ not y ]
  return (r, c)


fullAddM :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => Bit -> Bit -> Bit -> m (Bit, Bit)
fullAddM = fullAddM_explicit

fullAddM_half :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => Bit -> Bit -> Bit -> m (Bit, Bit)
fullAddM_half x y z = do
  (r1,c1) <- halfAddM x y
  (r2,c2) <- halfAddM r1 z
  return (r2, c1 || c2)
  
fullAddM_explicit :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => Bit -> Bit -> Bit -> m (Bit, Bit)
fullAddM_explicit x y z = do
  r <- xorN [x, y, z] -- 8 clauses
  -- c <- fuN ( \ xs -> 2 <= sum ( map fromEnum xs )) [x,y,z]
  c <- exists
  assert_implies [x,y] [c]
  assert_implies [x,z] [c]
  assert_implies [y,z] [c]
  assert_implies [not x, not y] [not c]
  assert_implies [not y, not z] [not c]
  assert_implies [not x, not z] [not c]
  return (r,c)

assert_implies :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => [Bit] -> [Bit] -> m ()
assert_implies xs ys =
  assertClause $ map not xs ++ ys

xorN :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => [Bit] -> m Bit
xorN = fuN $ foldr (/=) False

fuN :: forall (m :: * -> *) s. (HasSAT s, MonadState s m) => ([Bool] -> Bool) -> [Bit] -> m Bit
fuN f xs = do
  out <- exists
  let val = P.bool not id
  forM_ (sequence $ replicate (length xs) [False,True]) $ \ fs -> do
    assert_implies ( zipWith val fs xs )
                   [ val (f fs) out ]
  return out
