{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module Ersatz.Internal.Formula.Display where

import Ersatz.Internal.Formula
import Ersatz.Internal.Literal
import Ersatz.Problem (runSAT', formula)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Foldable (toList)
import Data.List (foldl', tails, sort)
import System.Process.Text
import Data.Text (Text)
import qualified Data.Text as T
import Data.Monoid
import Control.Monad (void, guard)
import Control.Lens

newtype V = V Int deriving (Eq, Ord)
instance Show V where show (V i) = "v" ++ show i

newtype C = C Int deriving (Eq, Ord)
instance Show C where show (C i) = "c" ++ show i

graph_ :: Formula -> Graph V V
graph_ f =  foldl' (flip add) (empty False) $ do
  c <- toList $ formulaSet f
  let x : ys = sort $ map (abs . literalId) $ clauseLiterals c
  y <- ys 
  return (V x, V y)

-- | bipartite graph of a CNF. variables and clauses are nodes.
-- an edge is drawn if a variable appears in a clause

digraph_ :: Formula -> Graph V C
digraph_ f = foldl' (flip add) (empty True) $ do
  (ck, c) <- zip  [1..] $ toList $ formulaSet f
  v <-  map (abs . literalId) $ clauseLiterals c
  return (V v, C ck)

-- * graphs

data Graph u v =
  Graph { directed :: ! Bool
        , fore :: ! (M.Map u (S.Set v))
        , back :: ! (M.Map v (S.Set u))
        } deriving Show

empty :: Bool -> Graph u v
empty d = Graph { directed = d, fore = M.empty, back = M.empty }

add :: (Ord v, Ord u) => (u, v) -> Graph u v -> Graph u v
add (u, v) g = g
  { fore = M.insertWith S.union u (S.singleton v) $ fore g
  , back = M.insertWith S.union v (S.singleton u) $ back g
  }  

edges :: Graph u v -> [(u,v)]
edges g = do
  (x,s) <- M.toList $ fore g
  y <- S.toList s
  return (x,y)

sources g = M.keys $ fore g
targets g = M.keys $ back g

toDot :: (Ord u, Ord v, Show u, Show v) => Graph u v -> Text
toDot g = T.unlines
   $ "graph Formula { node [shape=plaintext];"
   :  do (x,y) <- edges g
         return $ T.pack (show x) <> " -- " <> T.pack (show y) <> ";"
   ++ [ "}" ]

call prog t = void $ readProcessWithExitCode prog [ "-Tx11" ] t

dot t = displayWith "dot" t
neato t = displayWith "neato" t
fdp t = displayWith "fdp" t

displayWith prog = call prog 

graph = toDot . graph_ . form
digraph = toDot . digraph_ . form

form m = snd ( runSAT' m ) ^. formula 
