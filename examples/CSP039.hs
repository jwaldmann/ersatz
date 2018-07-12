-- | http://csplib.org/Problems/prob039/

{-# language FlexibleInstances, UndecidableInstances
  , TupleSections, GeneralizedNewtypeDeriving , TypeFamilies
  , PatternSignatures
#-}

import Prelude hiding (and,or,not,(&&),(||),any,all)
import qualified Prelude as P
import Ersatz
import qualified Ersatz.Counting as C

import qualified Data.Array as A
import Data.Ix
import Data.List (transpose)
import Control.Monad (forM)
import Control.Monad.State

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

solve inst = do
  let go b = do
        putStrLn $ "upper bound " ++ show b
        out <- solveWith minisat $ rehearsal film1 b
        case out of
          ( Satisfied
            , Just (sched :: Matrix Day Piece Bool, total::Integer)) -> do
             print total
             print $ map fst $ filter snd $ assocs sched
             go $ pred total
  go $ upperbound inst

-- | pay all actors on all days
upperbound inst =
  ( sum $ A.elems $ dura inst ) * ( sum $ A.elems $ cost inst )

rehearsal
  :: (MonadState s m, HasSAT s)
  => Instance -> Integer
  -> m (Matrix Day Piece Bit, Bits)
rehearsal inst bound = do
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

  let use :: Matrix Day Actor Bit
      use = mtimes sched $ ( encode <$> need inst )

      idle = fromLList (bounds use) $ transpose $ do
        col <- columns use
        let inc = drop 1 $ scanl (||) false col
            dec = scanr (||) false col
            pay = zipWith (&&) inc dec
        return $ zipWith (&&) pay $ map not col
  
  let total = balanced_sum $ do
        ((d,a),i) <- assocs idle
        return $ switch i $ times_constant ( cost inst A.! a )
                                           ( duration A.! d ) 

  assert $ total <=? encode bound
  
  return (sched, total)

balanced_sum :: [Bits] -> Bits
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


times_constant :: Integer -> Bits -> Bits
times_constant 0 b = encode 0
times_constant c b =
  let p = shift $ times_constant (div c 2) b
  in  if odd c then p + b else p

shift (Bits xs) = Bits (false : xs)

switch :: Bit -> Bits -> Bits
switch x (Bits ys) = Bits (map (x &&) ys)

bitwidth :: Bits -> Int
bitwidth (Bits xs) = length xs

class Semiring r where
  zero :: r ; plus  :: r -> r -> r
  one  :: r ; times :: r -> r -> r

instance Boolean b => Semiring b where
  zero = false ; plus = (||) ; one = true ; times = (&&)

newtype Matrix x y w = Matrix (A.Array (x,y) w) deriving Show

instance Functor (Matrix x y) where
  fmap f (Matrix a) = Matrix (fmap f a)

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

rows m = map snd $ ixrows m
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
          return ((x,z), balanced_fold zero id plus $ do
            y <- A.range (ylo,yhi)
            return $ times (a A.! (x,y)) (b A.! (y,z)) )
        _ -> error $ "huh: " ++ show (A.bounds a, A.bounds b)

is_permutation
  :: (Ix x, Ix y, b ~ Bit )
  => Matrix x y b -> b
is_permutation m =
  all (exactly_one) (rows m) && all (exactly_one) (columns m)

exactly_one :: Boolean b => [b] -> b
exactly_one xs =
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
