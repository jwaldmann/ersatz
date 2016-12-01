{-
tests formulas that are being generated
for comparison of bit strings.
-}

import Prelude hiding ((&&),(||),not,and,or)
import Ersatz
import Ersatz.Bit.Display
import Control.Monad (replicateM)

d4 = display $ do
  a <- exists
  b <- exists
  return $ (a :: Bit4) >=? b

d n = display $ do
  a <- make n
  b <- make n
  return $ a >=? b

d' n = display $ do
  a <- make n
  b <- make n
  return $ ge a b

ge (Bits a) (Bits b) = let (g,e) = geq a b in g || e
gt (Bits a) (Bits b) = fst $ geq a b

geq [] [] = (false,true)
geq (x:xs) (y:ys) =
  let (g,e) = geq xs ys
  in  (g || e && x && not y, e && eq x y)

eq x y = (x || not y) && (not x || y)

exactlyone_linear :: Boolean b => [b] -> b
exactlyone_linear xs = snd $ zol xs

zol [] = (true,false)
zol (x:xs) =
  let (z,o) = zol xs in (z && not x, z && x || o && not x )

exactlyone_binary :: Boolean b => [b] -> b
exactlyone_binary xs = snd $ zob xs

zob [] = (true,false)
zob [x] = (not x,x)
zob xs =
  let (lo,hi) = splitAt (div (length xs) 2) xs
      (zlo,olo) = zob lo
      (zhi,ohi) = zob hi
  in  (zlo && zhi, zlo && ohi || zhi && olo)

make n = Bits <$> replicateM n exists  


