-- | (minimal) dominating set on the knight's graph,
-- cf. http://oeis.org/A006075

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
import qualified Control.Concurrent.Async as A
import qualified Data.Array as A
import System.Random

main :: IO ()
main = getArgs >>= \ case
  [ "local", n ] -> void $ anneal  3 (read n)
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

anneal w n = do
  let a = A.listArray ((1,1),(n,n)) $ repeat True
  improve w a 0

pick xs = (xs !!) <$> randomRIO (0,length xs-1)

biased_pick [x] = return x
biased_pick (x:xs) = do
  f<- randomRIO (0,2::Int)
  if f == 0 then return x else biased_pick xs

instance (Random a, Random b) => Random (a,b) where
  randomRIO ((u,l),(o,r)) = 
    (,) <$> randomRIO (u,o) <*> randomRIO (l,r)

threshold = 10

add_randoms k a = do
  ps <- replicateM k $ randomRIO $ A.bounds a
  return $ a A.// zip ps (repeat True)

improve w a t | t > threshold = improve (w+1) a 0
improve w a t = do
  display ( show (w,t)) a Nothing
  out <- Par.firstJust $ replicate 8 $ improve_step w a
  case out of
     Just b -> improve w b 0
     Nothing -> do
       -- a <- add_randoms 1 a
       improve w a (t+1)

improve_step w a = do
  let verbose = False
  (ks, bp) <- pick $ bordered_patches w a
  let s = length ks
  when verbose $ display ("improve ..." ++ show w) a $ Just bp
  mq <- local Sortnet (s - 1) bp
  case mq of
    Nothing -> return Nothing
    Just q -> do
      let c = a A.// zip ks (repeat False) A.// filter snd (A.assocs q)
      when verbose $ display " ... improved" c $ Just q
      return $ Just c

bordered_patches w a = do
  ul@(u,l) <- A.indices a
  let or@(o,r) = (u+w-1,l+w-1)
  guard $ A.inRange (A.bounds a) or
  let inner = (ul,or)
  let inner_knights = do 
         k <- A.range inner
         guard $ at a k
         return k
  let a_without_inner = a A.// zip inner_knights (repeat False)
  let outer = ((u-2,l-2),(o+2,r+2))
  return (inner_knights, A.array outer $ do
    p <- A.range outer
    let is_covered = not (A.inRange (A.bounds a) p)
                 || P.any (at a_without_inner) (closed_neighbours p)
    return (p, is_covered) )

-- | a set that dominates the False cells of  a,
-- and has at most  s  elements.
local :: Method
      -> Int
      -> A.Array (Int,Int) Bool
      -> IO (Maybe (A.Array (Int,Int) Bool))
local how s a = do
  (status, Just result) <- solveWith minisat $ do
    u <- A.listArray (A.bounds a)
        <$> replicateM (A.rangeSize $ A.bounds a) exists
    assert_atmost how s $ A.elems u
    forM_ (A.assocs a) $ \ (p,x) -> 
      if x 
      then assert $ not $ at u p
      else do
        assert $ any ( \ q -> at u q ) $ closed_neighbours p
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
           Just p -> A.inRange (A.bounds p) (x,y)
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
  when True $ break_symmetries 
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

  assert_atmost how s $ concat b
  -- assert_atmost how s $ concat $ transpose b
  
  let onboard (x,y) = 0 <= x P.&& x < w P.&& 0 <= y P.&& y < w
      get (x,y) = if onboard (x,y) then b !! x !! y else false
      positions = (,) <$> [0..w-1] <*> [0..w-1]
  forM_ positions $ \ p ->
    assertClause $ get p : map get (neighbours p)
  return b

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
      b = ((1::Int,1::Int),(w,w))
      a = A.listArray ((1,1),(w,w)) $ concat xss
      next a = do
        (p,True) <- A.assocs a
        let b = a A.// [(p,False)]
        -- guard $ dominated b
        guard $ and $ (P.any (at b) $ neighbours p) : do 
           q <- neighbours p
           guard $ A.inRange (A.bounds b) q
           return $ P.any (at b) $ closed_neighbours q
        return b
      go a = case next a of
         [] -> a
         b:_ -> go b
      out = go a
  in  map (\x-> map (\y -> out A.!(x,y)) [1..w]) [1..w]

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
