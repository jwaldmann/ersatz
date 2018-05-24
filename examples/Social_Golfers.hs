-- | The Social Golfers Problem:
-- for each of w weeks, arrange golfers in g groups of p members
-- such that no two golfers are in the same group more than once.
-- See also papers by
-- Markus Triska at https://www.metalevel.at/

{-# language LambdaCase, PatternSignatures, TupleSections,
  GeneralizedNewtypeDeriving, StandaloneDeriving
#-}

import Prelude hiding (not,and,or,any,all,(&&),(||))
import Ersatz
import Ersatz.Counting
import qualified AMO

import qualified Data.Array as A
import Data.Ix
import Data.List (tails)
import Control.Monad (forM, forM_, when, guard )
import Text.Printf
import System.Environment

main = getArgs >>= \ case
  [] -> run 5 3 7
  [g, p, w] -> run (toEnum $ read g) (toEnum $ read p) (toEnum $ read w)

newtype Group = Group Int deriving (Read, Show, Enum, Ix, Eq, Ord, Num)
newtype Position = Position Int deriving (Read, Show, Enum, Ix, Eq, Ord, Num)
newtype Player = Player Int  deriving (Read, Show, Enum, Ix, Eq, Ord, Num)
newtype Week = Week Int deriving (Read, Show, Enum, Ix, Eq, Ord, Num)

fixed_assignments = True
symmetry_breaking_weeks = True
symmetry_breaking_players = False

run :: Group -> Position -> Week -> IO ()
run g p w = do
  let groups = [1 .. g ]
      positions = [1 .. p]
      default_group_of pl = toEnum $ 1 + div (fromEnum pl - 1) (fromEnum p)
      top_player = toEnum $ fromEnum g * fromEnum p
      players = [1 .. top_player ]
      weeks = [1 .. w]
  (status, msol@(Just sch)) <- 
      solveWith minisat $ do
        let bnd = ((1,1,1),(g,top_player,w))
  	sch :: A.Array (Group, Player, Week) Bit
    	  <- A.array bnd <$> forM ( A.range bnd ) ( \ ix -> (ix,) <$> exists )
        let bits_for_week w =
              for groups $ \ g -> for players $ \ pl -> sch A.! (g,pl,w)
            bits_for_player p = groups >>= \ g ->
                                weeks >>= \ w ->
                                return $ sch A.! (g, p, w)
	when fixed_assignments $ do
  	  -- fixed assignment for first week  
	  assert $ foreach players $ \ pl ->
	         foreach groups $ \ gr ->
		 sch A.! (gr,pl,1) === bool (gr == default_group_of pl)
          -- fixed assignment for players after second week
	  assert $ foreach (drop 1 weeks) $ \ w ->
	    foreach [1 .. min (fromEnum g) (fromEnum p) ] $ \ i ->
	        sch A.! (toEnum i, toEnum i, w)

        when symmetry_breaking_weeks $ do
          -- symmetry breaking for each weak
  	  assert $ foreach weeks $ \ w -> monotonic (bits_for_week w)
	  -- symmetry breaking over all weeks
	  assert $ monotonic $ for weeks $ \ w -> concat $ bits_for_week w

        when symmetry_breaking_players $ do
          assert $ monotonic $ for players bits_for_player
          
  	assert $ foreach weeks $ \ w ->
           foreach players $ \ p ->
           exactly 1 $ for groups $ \ g -> sch A.! (g,p,w)
  	assert $ foreach weeks $ \ w ->
           foreach groups $ \ g ->
	   exactly (fromEnum p) $ for players $ \ p -> sch A.! (g,p,w)
        forM_ (selections 2 players) $ \ [p,q] ->
  	   -- assert $ atmost 1
	   AMO.assert_atmost_one AMO.Plain
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
	     p <- players
	     guard $ sch A.! (g,p,w)
	     return $ printf "%2d" $ fromEnum p

monotonic :: [[Bit]] -> Bit
monotonic = monotonic_balanced

monotonic_balanced [] = true
monotonic_balanced [x] = true
monotonic_balanced [x,y] = x >? y
monotonic_balanced xs =
  let (pre, this : post) = splitAt (div (length xs) 2) xs
  in  monotonic_balanced (pre ++ [this]) && monotonic_balanced ([this] ++ post)

monotonic_linear xs = and $ zipWith (>?) xs $ tail xs
monotonic_quadratic xs = and $ for (selections 2 xs) $ \ [x,y] -> x >? y

for xs f = f <$> xs

foreach xs p = all p xs

selections :: Int -> [a] -> [[a]]
selections 0 xs = return []
selections k (x:xs) =
  selections k xs ++ ( (x:) <$> (selections (k-1) xs) )
selections _ _ = []
