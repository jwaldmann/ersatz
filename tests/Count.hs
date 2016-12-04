import Prelude hiding ((&&),(||),not,and,or)
import Ersatz
import Ersatz.Counting
import Ersatz.Bit
import Ersatz.Bits
import Ersatz.Codec
import Ersatz.Equatable
import Ersatz.Orderable
import qualified Ersatz.Bit.Display as B
import qualified Ersatz.Internal.Formula.Display as F
import Control.Monad (replicateM)

count n = do
  xs <- replicateM (2*n) exists
  assert $ exactly n xs

factor n = do
  let w = truncate $ logBase 2 $ fromIntegral n
  a <- make w ; b <- make w
  assert $ a >=? 2 ; assert $ b >=? 2
  assert $ times a b === encode (fromIntegral n)
  return (a,b)

make n = Bits <$> replicateM n exists

times (Bits xs) (Bits ys) = Bits (mul xs ys)

mul [] ys = []
mul (x:xs) ys = add (map (&& x) ys) $ false : mul xs ys

add xs ys =
  let go c [] [] = [c]
      go c (x:xs) [] = let (r,d) = halfadd c x in r : go d xs []
      go c [] (y:ys) = let (r,d) = halfadd c y in r : go d ys []
      go c (x:xs) (y:ys) = let (r,d) = fulladd c x y in r : go d xs ys
  in  go false xs ys
      
halfadd x y = (xor x y , x && y)

fulladd x y z =
  let (r , c)  = halfadd x y
      (s , d) = halfadd r z
  in  (s, c || d)
