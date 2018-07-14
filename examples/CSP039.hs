-- | http://csplib.org/Problems/prob039/

{-# language FlexibleInstances, UndecidableInstances, LambdaCase
  , TupleSections, GeneralizedNewtypeDeriving , TypeFamilies
  , PatternSignatures, ScopedTypeVariables, FlexibleContexts
#-}

import Prelude hiding (and,or,not,(&&),(||),any,all)
import qualified Prelude as P
import Ersatz
import Ersatz.NBV
import GHC.TypeLits
import qualified Ersatz.Counting as C

import qualified Data.Array as A
import Data.Ix
import Data.List (transpose, tails)
import qualified Data.Set as S
import Control.Monad (forM)
import Control.Monad.State
import Data.Reflection
import Data.Proxy

import Control.Concurrent.Async
import GHC.Conc

newtype Day   = Day   Int deriving (Eq, Ord, Ix, Num, Show)
newtype Piece = Piece Int deriving (Eq, Ord, Ix, Num, Show)
newtype Actor = Actor Int deriving (Eq, Ord, Ix, Num, Show)


{-
 Day     1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 20 Cost/100
Actor 1  1 1 1 1 0 1 0 1 0  1 1 0 0 0 0 0 0 0 0  0 10
Actor 2  1 1 1 0 0 0 1 1 0  1 0 0 1 1 1 0 1 0 0  1  4
Actor 3  0 1 1 0 1 0 1 1 0  0 0 0 1 1 1 0 0 0 0  0  5
Actor 4  0 0 0 0 0 0 0 0 0  1 1 1 1 0 0 0 0 0 0  0  5
Actor 5  0 1 0 0 0 0 1 1 0  0 0 1 0 1 0 0 0 1 1  1  5
Actor 6  0 0 0 0 0 0 0 0 0  0 0 0 0 1 1 1 1 1 0  0 40
Actor 7  0 0 0 0 1 0 1 1 0  0 0 0 0 0 1 0 0 0 0  0  4
Actor 8  0 0 0 0 0 1 1 1 1  0 0 0 0 0 0 0 0 0 0  0 20
Duration 2 1 1 1 1 3 1 1 1  2 1 1 2 1 2 1 1 2 1  1
-}

data Instance = Instance
  { cost :: A.Array Actor Integer
  , need :: Matrix Piece Actor Bool
  , dura :: A.Array Piece Integer
  } deriving Show

film1 = Instance
  { cost = A.listArray (Actor 1, Actor 8)
      [ 10, 4, 5, 5, 5, 40, 4, 20 ]
  , dura = A.listArray (Piece 1, Piece 20)
      [ 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1 ]
  , need = fromLList ((Piece 1, Actor 1),(Piece 20, Actor 8))
      $ transpose $ map (map toEnum)
      [[1,1,1,1,0,1,0,1,0,1,1,0,0,0,0,0,0,0,0,0]
      ,[1,1,1,0,0,0,1,1,0,1,0,0,1,1,1,0,1,0,0,1]
      ,[0,1,1,0,1,0,1,1,0,0,0,0,1,1,1,0,0,0,0,0]
      ,[0,0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0]
      ,[0,1,0,0,0,0,1,1,0,0,0,1,0,1,0,0,0,1,1,1]
      ,[0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,0,0]
      ,[0,0,0,0,1,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0]
      ,[0,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0]
      ]
  }

main = do
  solve film1

solve inst = solve_from inst $ upperbound inst

solve_from inst bound = do
  t <- getNumCapabilities
  as <- forM (take t [0 ..]) $ \ d ->
    async $ solve_below inst $ bound - (2^d)
  waitAnyCancelJust as >>= \ case
    Nothing -> error "huh"
    Just b -> solve_from inst b

waitAnyCancelJust as = do
  let go [] = return Nothing
      go as = do
         (this,res) <- waitAny as
         case res of 
           Nothing -> go $ filter (/= this) as
           Just x ->  do forM_ as cancel ; return $ Just x
  go as

solve_below inst bound = do
    putStrLn $ "upper bound " ++ show bound  
    reifyNat (fromIntegral $ bitwidth $ encode bound) $ \ p -> do
    out <- solveWith minisat $ rehearsal p inst bound
    case out of
      ( Satisfied , Just (sched :: Matrix Day Piece Bool, total :: Integer)) -> do
        print total
        print $ map fst $ filter snd $ assocs sched
        return $ Just total
      _ -> return Nothing


-- | pay all actors on all days
upperbound inst =
  ( sum $ A.elems $ dura inst ) * ( sum $ A.elems $ cost inst )

rehearsal
  :: (MonadState s m, HasSAT s, KnownNat w)
  => Proxy w -> Instance -> Integer
  -> m (Matrix Day Piece Bit, NBV w)
rehearsal p inst bound = do
  let (Piece lo, Piece hi) = A.bounds $ dura inst
  
  sched :: Matrix Day Piece Bit
    <- mfree exists ((Day lo, Piece lo),(Day hi, Piece hi))
  assert $ is_permutation sched

  let days = (Day lo, Day hi)
  let width :: Int
      width = maximum $ map (bitwidth . encode) $ A.elems $ dura inst
      bits w = Bits <$> replicateM w exists
  duration :: A.Array Day Bits <-
    A.array days <$> forM (A.range days) (\d -> (d,) <$> bits width)
  forM_ (assocs sched) $ \  ((d,p),f) ->
    assert $ f ==> ( duration A.! d === encode (dura inst A.! p ))

  let (alo, ahi) = A.bounds $ cost inst
  use :: Matrix Day Actor Bit <- mfree exists ((Day lo, alo),(Day hi, ahi))
  -- let use = mtimes sched $ ( encode <$> need inst )
  forM_ (assocs sched) $ \ ((d,p),f) -> 
    -- assert $ f ==> row use d === (map encode $ row (need inst) p)
    forM_ (zip (row use d) (row (need inst) p)) $ \ (u,n) -> 
      assert $ f ==> (u === encode n)

  let idle = fromLList (bounds use) $ transpose $ do
        col <- columns use
        let inc = drop 1 $ scanl (||) false col
            dec = scanr (||) false col
            pay = zipWith (&&) inc dec
        return $ zipWith (&&) pay $ map not col


  let pieces = A.range (Piece lo, Piece hi)
  let actors = A.indices $ cost inst
      needs p = S.fromList $ filter (\a -> need inst ! (p,a)) actors
  -- | notation as in paper:
  -- in case that  needs(j) = needs(i) + { s } ,
  -- a benchmark for (i,j) is any other piece that needs s.
  -- for all other cases, the set of benchmarks is empty.
  let benchmarks i j = do
        guard $ S.isSubsetOf (needs i) (needs j)
        case S.toList $ S.difference (needs j) (needs i) of
          [ s ] ->
            (s,) <$> filter ( \ b -> b /= j && need inst ! (b,s) ) pieces
          _ -> []
      has_benchmarks i = S.fromList $ do
        j <- pieces
        (s,b) <- benchmarks i j
        return s

  forM_ pieces $ \ p ->
    forM_(has_benchmarks p) $ \ s -> 
      forM_ days $ \ d ->
        assert $ not $ sched ! (d,p) && idle ! (d,s)
  
  let total = balanced_sum $ do
        let ((dlo,alo),(dhi,ahi)) = bounds idle
        a <- A.range (alo,ahi)
        return $ (*) (encode $ cost inst A.! a) $ balanced_sum $ do
          d <- A.range (dlo,dhi)
          let i = idle ! (d,a)
          return $ nbv $ switch i $ duration A.! d

  assert $ total <=? nbv (encode bound)
  
  return (sched, total)

subsequences 0 xs = return []
subsequences d [] = []
subsequences d (x:xs) =
  subsequences d xs ++ map (x:) (subsequences (d-1) xs)

balanced_sum :: (Num b, Num (Decoded b), Codec b) => [b] -> b
balanced_sum xs = balanced_fold (encode 0) id (+) xs

balanced_fold :: r -> (a -> r) -> (r -> r -> r) -> [a] -> r
balanced_fold z u b xs =
  let go [] = z
      go [x] = u x
      go xs = let (ys,zs) = parts xs in b (go ys) (go zs)
  in  go xs

parts :: [a] -> ([a],[a])
parts [] = ([],[])
parts (x:xs) = let (ys,zs) = parts xs in (x:zs,ys)

switch :: Bit -> Bits -> Bits
switch x (Bits ys) = Bits (map (x &&) ys)

bitwidth :: Bits -> Int
bitwidth (Bits xs) = length xs

class Semiring r where
  zero :: r ; plus  :: r -> r -> r
  plus_many :: [r] -> r
  one  :: r ; times :: r -> r -> r

instance Boolean b => Semiring b where
  zero = false ; plus = (||) ; plus_many = or
  one = true ; times = (&&)

newtype Matrix x y w = Matrix (A.Array (x,y) w) deriving Show

instance Functor (Matrix x y) where
  fmap f (Matrix a) = Matrix (fmap f a)

Matrix a ! i = a A.! i

assocs (Matrix a) = A.assocs a
bounds (Matrix a) = A.bounds a

ixrows :: (Ix x, Ix y) => Matrix x y w -> [(x,[w])]
ixrows (Matrix a ) = do
  let ((xlo,ylo),(xhi,yhi)) = A.bounds a
  x <- A.range (xlo,xhi)
  return (x, map (\ y -> a A.! (x,y)) $ A.range (ylo,yhi))

ixcolumns :: (Ix x, Ix y) => Matrix x y w -> [(y,[w])]
ixcolumns (Matrix a ) = do
  let ((xlo,ylo),(xhi,yhi)) = A.bounds a
  y <- A.range (ylo,yhi)
  return (y, map (\ x -> a A.! (x,y)) $ A.range (xlo,xhi))

row m x = 
  let ((xlo,ylo),(xhi,yhi)) = bounds m 
  in map (\y -> m ! (x,y)) $ A.range (ylo,yhi)
rows m = map snd $ ixrows m
column m y = 
  let ((xlo,ylo),(xhi,yhi)) = bounds m 
  in map (\x -> m ! (x,y)) $ A.range (xlo,xhi)
columns m = map snd $ ixcolumns m

instance (Ix x, Ix y, Codec a) => Codec (Matrix x y a) where
  type Decoded (Matrix x y a) = Matrix x y (Decoded a)
  encode (Matrix a) = Matrix (encode a)
  decode s (Matrix a) = Matrix <$> decode s a

fromLList :: (Ix x, Ix y) => ((x,y),(x,y)) -> [[w]] -> Matrix x y w
fromLList bnd @ ((xlo,ylo),(xhi,yhi)) wss =
  Matrix $ A.array bnd $ do
    (x,ws) <- strict_zip (A.range (xlo,xhi)) wss
    (y,w) <- strict_zip (A.range (ylo,yhi)) ws
    return ((x,y),w)

strict_zip xs ys | length xs == length ys = zip xs ys

mfree ::  (Ix x, Ix y, Monad m)
  => m w -> ((x,y),(x,y)) -> m (Matrix x y w)
mfree make bnd =
  ( Matrix . A.array bnd ) <$> forM (A.range bnd) ( \ i ->
      (i,) <$> make )

mtimes ::  (Ix x, Ix y, Ix z, Semiring w, Show x, Show y, Show z )
  => Matrix x y w -> Matrix y z w -> Matrix x z w
mtimes (Matrix a) (Matrix b) =
  let ((xlo,ylo),(xhi,yhi)) = A.bounds a
      ((ylo',zlo),(yhi',zhi)) = A.bounds b
      bnd = ((xlo,zlo),(xhi,zhi))
  in  case ylo == ylo' && yhi == yhi' of
        True -> Matrix $ A.array bnd $ do
          (x,z) <- A.range bnd
          return ((x,z), plus_many $ do
            y <- A.range (ylo,yhi)
            return $ times (a A.! (x,y)) (b A.! (y,z)) )
        _ -> error $ "huh: " ++ show (A.bounds a, A.bounds b)

is_permutation
  :: (Ix x, Ix y, b ~ Bit )
  => Matrix x y b -> b
is_permutation m =
  all (exactly_one) (rows m) && all (exactly_one) (columns m)

exactly_one :: [Bit] -> Bit
exactly_one = exactly_one_1

exactly_one_2 = C.exactly 1

exactly_one_0 xs = or xs && and ( do
 x : ys <- tails xs ; y <- ys ; return $ not $ x && y )

exactly_one_1 xs =
  let go [] = (true, false)
      go [x] = (not x, x)
      go xs =
        let (ys,zs) = parts xs
            (zero_ys,one_ys) = go ys
            (zero_zs,one_zs) = go zs
        in  ( zero_ys && zero_zs
            , one_ys && zero_zs || zero_ys && one_zs
            )
  in  snd $ go xs          
