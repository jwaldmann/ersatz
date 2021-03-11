{-# language LambdaCase, PatternSignatures, BangPatterns #-}

import System.Environment
import Prelude hiding (and,or,not)
import Ersatz
import qualified Data.Array as A
import qualified Data.IntSet as I
import Data.List (inits,tails,sort)
import Control.Monad (when)
import Data.Coerce

type N = Int
type C = Int

main = getArgs >>= \ case
  [] -> mainFor [3,3] 5
  xs -> mainFor (map read $ init xs) (read $ last xs)
  
mainFor xs n = do
  let nodes = [1..n]
      col :: C = fromIntegral $ length xs
      colors = [1..col]

  out <- solveWith minisat $ do
    let bnd = ((1,1,1),(n,n,col))
    f :: A.Array (N,N,C) Bit <- traverse (\ _ -> exists)
      $ arrayf bnd $ const ()

    let deg = arrayf ((1,1),(n,col)) $ \ (x,c) ->
          sumBits $ map (\ y -> f A.! (y,x,c)) [1..x-1]
                 <> map (\ y -> f A.! (x,y,c)) [x+1..n]

    assert $ and $ do 
      (x,y) <- cliques2 nodes
      return $ or $ do
        c <- colors; return $ f A.! (x,y,c)
      
    sequence_ $ do
      (c,x) <- zip colors xs
      return $ forCliques x (coerce nodes) $ \ clq -> 
        assert $ or $ do
          -- [x,y] <- cliques 2 $ coerce $ I.toList clq
          (x,y) <- cliques2 $ coerce $ I.toList clq
          return $ not $ f A.! (x,y,c)
        
    return f
  case out of
    (Satisfied, Just (f :: A.Array (N,N,C) Bool)) -> do
      putStrLn $ unlines $ do
        x <- nodes
        return $ unwords $ do
          y <- nodes
          return
            $ if x < y
            then show ( fromEnum $ colof f x y  )
            else "."

colof f x y = head $ filter (\c -> f A.! (x,y,c)) [1..]

monotones (x:y:ys) = (x <=? y) : monotones (y:ys)
monotones _ = []

cliques2 xs = do
  x:ys <- tails xs
  y <- ys
  return (x,y)

type Clique = I.IntSet
             
forCliques
  :: (Eq k, Num k, Monad m)
  => k -> [Int] -> (Clique -> m ())
  -> m ()
forCliques k xs act =
  let go !0 xs !c = act c
      go !k [] !c = return ()
      go !k (x:xs) !c = do
        go k xs c
        go (k-1) xs (I.insert x c)
  in  go k xs I.empty      

arrayf bnd f = A.array bnd $ map (\i -> (i, f i)) $ A.range bnd
