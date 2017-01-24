{-# LANGUAGE FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language NoMonomorphismRestriction #-}

import Prelude hiding (and,or,not,(&&),(||))
import qualified Prelude as P
import qualified Data.Bool as P
import Ersatz
import Control.Monad
import Control.Monad.State
import System.Environment
import Data.Foldable (toList)

main :: IO ()
main = getArgs >>= \ case
  [ how, w, s ] -> do
    (stats, ~(Satisfied, msol@(Just b))) <- solveWithStats minisat
        $ problem (case how of
             "sumBit" -> return . sumBit
             "sumBits" -> return . sumBits
             "sumBitsM" -> sumBitsM
          ) (read w) (read s)
    print stats    
    mapM_ print $ map (map fromEnum) b

-- | dominating set of  s  knights on  w*w  board
problem :: (MonadState s m, HasSAT s)
  => ( [Bit] -> m Bits ) -> Int -> Int 
  -> m [[Bit]]
problem sumbits w s = do
  b <- replicateM w $ replicateM w exists
  su <- sumbits $ concat b
  assert $ encode (fromIntegral s) >=? su
  let onboard (x,y) = 0 <= x P.&& x < w P.&& 0 <= y P.&& y < w
      get (x,y) = if onboard (x,y) then b !! x !! y else false
      positions = (,) <$> [0..w-1] <*> [0..w-1]
      neighbours (x,y) = do
        (dx,dy) <- (,) <$> [-2..2] <*> [-2..2]
        guard $ dx^2 + dy^2 == 5
        return (x+dx,y+dy)
  forM_ positions $ \ p ->
    assert $ or $ get p : map get (neighbours p)
  return b

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