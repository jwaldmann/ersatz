{-# language OverloadedStrings #-}
{-# language LambdaCase #-}

module Ersatz.Bit.Display where

import Ersatz.Bit (Bit(..))
import Ersatz.Internal.StableName
import Ersatz.Problem (runSAT')
import Control.Monad.RWS
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import System.IO.Unsafe
import Control.Lens
import Data.Foldable (toList)
import Data.Text (Text)
import qualified Data.Text as T
import System.Process.Text

display m = dot $ fst $ runSAT' m

dot b = void $ readProcessWithExitCode "dot" [ "-Tx11" ] $ toDot b

toDot :: Bit -> Text
toDot b = snd
  $ ( \ m -> evalRWS (do
       tell "digraph Bit {"
       tell "graph [ordering=\"out\"]"
       -- tell "node [style=\"rounded\", shape=box]"
       m
       tell "}"
    ) () s0 )
  $ walk b

subs :: Bit -> [Bit]
subs b = case b of
  Not (And xs) -> toList xs
  And xs -> toList xs
  Xor a b -> [a,b]
  Mux a b c -> [a,b,c]
  Not a -> [a]
  Var {} -> []
  Run {} -> []

name :: Bit -> Text
name b = case b of
  Not (And {}) -> "nand"
  And {} -> "and"
  Xor {} -> "xor"
  Mux {} -> "mux"
  Not {} -> "not"
  Var l -> T.pack $ show l
  Run {} -> "run"

data State = State
  { _stableMap :: !(HashMap (StableName ()) Int)
  , _next :: !Int
  }

s0 :: State
s0 = State { _stableMap = HashMap.empty , _next = 0 }

stableMap :: Lens' State (HashMap (StableName ()) Int)
stableMap f (s @ State {_stableMap = sm})
  = fmap (\ sm' -> s { _stableMap = sm'} ) (f sm)

next :: Lens' State Int
next f (s @ State { _next = n })
  = fmap (\ n' -> s { _next = n' } ) (f n)
  
fresh :: RWST () Text State Identity Int
fresh = do this <- use next ; next += 1 ; return this

walk :: Bit -> RWST () Text State Identity Int
walk b = do
  let sn = unsafePerformIO (makeStableName' b)
  use (stableMap.at sn) >>= \ case
    Just n -> return n
    Nothing -> do
      this <- fresh
      stableMap.at sn ?= this
      cs <- forM (subs b) walk
      tell $ T.pack (show this) <> "[label=\"" <> name b <> "\"];"
      forM_ cs $ \ c -> do
        tell $ T.pack (show this) <> "->" <> T.pack (show c) <> ";"
      return this
      
