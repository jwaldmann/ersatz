-- | (minimal) dominating set on the knight's graph,
-- cf. http://oeis.org/A006075

{-# LANGUAGE FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language NoMonomorphismRestriction #-}

import Prelude hiding (and,or,not,(&&),(||))
import qualified Prelude as P
import qualified Data.Bool as P
import Ersatz

import Exactly

import Control.Monad
import Control.Monad.State
import System.Environment
import Data.Foldable (toList)
import Data.List (transpose)
import qualified Control.Concurrent.Async as A
import qualified Data.Array as A

main :: IO ()
main = getArgs >>= \ case
  [ w, s ] -> void $ run methods (read w) (read s)
  [ w] -> search methods (read w)

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

present msg s xss = do
    putStrLn msg
    let form = unwords . map (\ case 0 -> "."; 1-> "K") 
    mapM_ (putStrLn . form) xss
    let c = sum $ map fromEnum $ concat xss
    putStrLn $ "actual number of knights is: " ++ show c
    when (c > s) $ error $ "what - " ++ show (sum $ concat xss)


-- | dominating set of  s  knights on  w*w  board
problem :: (MonadState s m, HasSAT s)
  => Method -> Int -> Int 
  -> m [[Bit]]
problem how w s = do
  b <- allocate w 
  break_symmetries [ transpose, reverse, map reverse ] b
  assert_symmetries ( --  transpose . reverse :
                     -- reverse . map reverse :
                     --  map reverse :
		     transpose :
		      reverse :
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

neighbours (x,y) = do
        (dx,dy) <- (,) <$> [-2..2] <*> [-2..2]
        guard $ dx^2 + dy^2 == 5
        return (x+dx,y+dy)
  
allocate w = replicateM w $ replicateM w exists

assert_symmetries ops b = do
  forM_ ops $ \ op -> 
    assert $ Bits (concat b) === Bits (concat $ op b)

break_symmetries ops b = do
  forM_ ops $ \ op -> 
    assert $ concat b <=? concat (op b)

-- * try to reduce a solution

dominated a = P.and $ do
  p <- A.indices a
  return $ P.or $ do
    q <- p : neighbours p
    return $ at a q

at a q = if A.inRange (A.bounds a) q then a A.! q else False

reduce xss = 
  let w = length xss
      b = ((1,1),(w,w))
      a = A.listArray ((1,1),(w,w)) $ concat xss
      next a = do
        (p,True) <- A.assocs a
        let b = a A.// [(p,False)]
        guard $ dominated b
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

unbits (Bits xs) = xs

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


fullAddM = fullAddM_explicit

fullAddM_half x y z = do
  (r1,c1) <- halfAddM x y
  (r2,c2) <- halfAddM r1 z
  return (r2, c1 || c2)
  
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

assert_implies xs ys =
  assertClause $ map not xs ++ ys

xorN = fuN $ foldr (/=) False

fuN f xs = do
  out <- exists
  let val = P.bool not id
  forM_ (sequence $ replicate (length xs) [False,True]) $ \ fs -> do
    assert_implies ( zipWith val fs xs )
                   [ val (f fs) out ]
  return out
