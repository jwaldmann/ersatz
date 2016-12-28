{-# language LambdaCase #-}

import Prelude hiding (and,or,not,(&&),(||))
import qualified Prelude as P
import Ersatz
import Control.Monad
import Control.Monad.State
import System.Environment

main :: IO ()
main = getArgs >>= \ case
  [ how, w, s ] -> do
    (Satisfied, msol@(Just b)) <- solveWith minisat
        $ problem (case how of
             "sumBit" -> sumBit; "sumBits" -> sumBits
          ) (read w) (read s)
    mapM_ print $ map (map fromEnum) b

-- | dominating set of  s  knights on  w*w  board
problem :: (MonadState s m, HasSAT s)
  => ( [Bit] -> Bits ) -> Int -> Int 
  -> m [[Bit]]
problem sumbits w s = do
  b <- replicateM w $ replicateM w exists
  assert $ encode (fromIntegral s) >=? sumbits (concat b)
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

