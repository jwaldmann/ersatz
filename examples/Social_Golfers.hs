-- | The Social Golfers Problem:
-- for each of w weeks, arrange golfers in g groups of p members
-- such that no two golfers are in the same group more than once.
-- See also papers by
-- Markus Triska at https://www.metalevel.at/

{-# language LambdaCase, PatternSignatures, TupleSections,
  GeneralizedNewtypeDeriving
#-}

import Prelude hiding (not,and,or,any,all,(&&),(||))
import Ersatz
import Ersatz.Counting

import qualified Data.Array as A
import Data.Ix
import Control.Monad (forM, when, guard )
import System.Environment

main = getArgs >>= \ case
  [] -> run 5 3 7
  [g, p, w] -> run (read g) (read p) (read w)

newtype Group = Group Int deriving (Read, Show, Enum, Ix, Eq, Ord, Num)
newtype Player = Player Int  deriving (Read, Show, Enum, Ix, Eq, Ord, Num)
newtype Week = Week Int deriving (Read, Show, Enum, Ix, Eq, Ord, Num)

run :: Group -> Player -> Week -> IO ()
run g p w = do
  let groups = [1 .. g ]
      positions = [1 .. p]
      players = (,) <$> groups <*> positions
      weeks = [1 .. w]
  (status, msol@(Just sch)) <- 
      solveWith minisat $ do
        let bnd = ((1,(1,1),1),(g,(g,p),w))
  	sch :: A.Array (Group, (Group,Player), Week) Bit
    	  <- A.array bnd <$> forM ( A.range bnd ) ( \ ix -> (ix,) <$> exists )
  	assert $ foreach weeks $ \ w ->
           foreach players $ \ p ->
           exactly 1 $ for groups $ \ g -> sch A.! (g,p,w)
  	assert $ foreach weeks $ \ w ->
           foreach groups $ \ g ->
	   exactly (fromEnum p) $ for players $ \ p -> sch A.! (g,p,w)
  	assert $ foreach (selections 2 players) $ \ [p,q] ->
           atmost 1
	 $ groups >>= \ g -> weeks >>= \ w ->
	   return $ sch A.! (g,p,w) && sch A.! (g,q,w)
        return sch
  case status of
    Satisfied -> do 
       putStrLn $ unlines $ do
         w <- weeks
	 return $ unwords $ do
	   g <- groups
	   "|" : do
	     gp <- players
	     guard $ sch A.! (g,gp,w)
	     let (gr,ps) = gp
	     return $ show $ (fromEnum gr - 1) * (fromEnum p) + fromEnum ps



for xs f = f <$> xs

foreach xs p = all p xs

selections :: Int -> [a] -> [[a]]
selections 0 xs = return []
selections k (x:xs) =
  selections k xs ++ ( (x:) <$> (selections (k-1) xs) )
selections _ _ = []