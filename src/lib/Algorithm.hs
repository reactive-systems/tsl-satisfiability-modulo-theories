-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm
-- Maintainer  :  Philippe Heim
--
-- This module implements the TSL-(TU)-SAT algorithm.
--
-----------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-----------------------------------------------------------------------------
module Algorithm
  ( sat
  , Result(..)
  ) where

-----------------------------------------------------------------------------
import BuechiStreamAutomaton
  ( BSA
  , ExplTrans
  , State
  , accepting
  , cells
  , effect
  , initial
  , lazyConstrainted
  , postTrans
  , states
  )

import Control.Monad (when)
import Data.Set (toList)
import Excludor as Exclude (Exclude, exclude, fromBSA, possible, size)
import FindFirstConcurrent (incParallelFirst)
import SMTQuery (SMTForm(..), SMTQuery, anySMTSat)

-----------------------------------------------------------------------------
-- | 'Block' is the search tree element of the algorithm
--
data Block =
  Block
      -- 'state' is the 'State' in the 'BSA'
    { state :: State
      -- 'parent' consists of the previous block and the transition
      -- from this previous block to the current one
    , parent :: Maybe (Block, ExplTrans)
    }
  deriving (Eq, Ord, Show)

-----------------------------------------------------------------------------
-- | The 'trace' of a 'Block' is the sequence of blocks from the root to
-- the current 'Block'
--
trace :: Block -> [Block]
trace b = reverse $ trace' b
  where
    trace' b@Block {parent = Nothing} = [b]
    trace' b@Block {parent = Just (p, _)} = b : trace' p

-----------------------------------------------------------------------------
-- | The 'transTrace' of a 'Block' is the sequence of transitions from the
-- root to the current 'Block'
--
transTrace :: Block -> [ExplTrans]
transTrace b = reverse $ trace' b
  where
    trace' Block {parent = Nothing} = []
    trace' Block {parent = Just (p, t)} = t : trace' p

-----------------------------------------------------------------------------
-- | 'nextBlocks' computes the successors of a 'Block' in the algorithms 
-- search
--
nextBlocks :: (Ord c, Ord f, Ord p) => BSA c f p -> Block -> [Block]
nextBlocks bsa b =
  [Block {state = q, parent = Just (b, t)} | (t, q) <- postTrans bsa (state b)]

-----------------------------------------------------------------------------
-- | 'tracePossible' generates an 'SMTQuery' to check whether some trace 
-- induced by a 'Block' is possible
--
tracePossible :: (Ord c, Ord p, Ord f) => BSA c f p -> Block -> SMTQuery c f p
tracePossible bsa b =
  let pred = toList (snd (effect bsa (transTrace b)))
   in [PPred p | (p, t) <- pred, t] ++ [NPred p | (p, t) <- pred, not t]

-----------------------------------------------------------------------------
-- | 'reccurentPos' generates an 'SMTQuery' for each possible accepting 
-- lasso (with the equality constraint)
--
reccurentPos :: (Ord c, Ord p, Ord f) => BSA c f p -> Block -> [SMTQuery c f p]
reccurentPos bsa b =
  let backtrace = [b' | b' <- trace b, state b == state b', b /= b']
      predQuery = tracePossible bsa b
   in if state b `elem` accepting bsa
        then fmap
               (\b' ->
                  Eqc
                    (fst (effect bsa (transTrace b)))
                    (fst (effect bsa (transTrace b'))) :
                  predQuery)
               backtrace
        else []

-----------------------------------------------------------------------------
-- | 'Result' represents the possible results of the algorithm
--
data Result
  = SAT
  -- ^ 'SAT' means –big surprise– that the formula is satisfiable
  | UNSAT_LTL
  -- ^ 'UNSAT_LTL' means that the formula is not satisfiable, even not
  -- the LTL approximation
  | UNSAT
  -- ^ 'UNSAT' means that the formula is no satisfiable, but the LTL
  -- approximation is
  deriving (Eq)

-----------------------------------------------------------------------------
-- | 'simpleSatSearch' performs the simple satisfiability search without
-- doing any exclusion. It therefore only terminates (of course not always) 
-- if the formula is satisfiable.
--
simpleSatSearch :: Bool -> BSA String String String -> IO (Maybe Result)
simpleSatSearch verbose bsa =
  let init = [Block {state = q, parent = Nothing} | q <- toList $ initial bsa]
   in loopSatSearch init
  where
    modBSA = lazyConstrainted bsa
    --
    loopSatSearch :: [Block] -> IO (Maybe Result)
    loopSatSearch =
      \case
        [] -> return Nothing
        x:xr -> do
          when verbose $ putStrLn $ "[SAT]  DEPTH: " ++ show (length $ trace x)
          querySat <- anySMTSat (toList $ cells modBSA) (reccurentPos modBSA x)
          if querySat
            then return $ Just SAT
            else loopSatSearch (xr ++ nextBlocks modBSA x)

-----------------------------------------------------------------------------
-- | 'fullSatSearch' preforms the full satisfiability search
--
fullSatSearch :: Bool -> BSA String String String -> IO (Maybe Result)
fullSatSearch verbose bsa =
  let init = [Block {state = q, parent = Nothing} | q <- toList $ initial bsa]
    -- ^ initial states of the BSA
      any = [Block {state = q, parent = Nothing} | q <- toList $ states bsa]
    -- ^ all states of the BSA (as starting block) for the exclusion
   in loopFull any (Exclude.fromBSA bsa) init
  where
    loopFull :: [Block] -> Exclude ExplTrans -> [Block] -> IO (Maybe Result)
    loopFull ys ex =
      \case
        [] ->
          if possible (fromBSA bsa) []
            then return $ Just UNSAT
            else return $ Just UNSAT_LTL
        x:xr -> do
          when verbose $
            putStrLn $
            "[FULL] " ++
            "DEPTH: " ++
            show (length $ trace x) ++ " EXCLUDED: " ++ show (Exclude.size ex)
          (ex', ys') <-
            case ys of
              [] -> return (ex, [])
              y:yr -> do
                queryExlude <-
                  anySMTSat (toList $ cells bsa) [tracePossible bsa y]
                if queryExlude
                  then return (ex, yr ++ nextBlocks bsa y)
                  else return (exclude ex (transTrace y), yr)
          querySat <- anySMTSat (toList $ cells bsa) (reccurentPos bsa x)
          let xs' =
                if possible ex' []
                  then if possible ex' (transTrace x)
                         then xr ++ nextBlocks bsa x
                         else xr
                  else []
          if querySat
            then return $ Just SAT
            else loopFull ys' ex' xs'

-----------------------------------------------------------------------------
-- | 'sat' preforms the satisfiability analysis by running both 
-- approaches concurrently
--
sat :: BSA String String String -> Bool -> IO Result
sat bsa verbose = do
  out <-
    incParallelFirst 2 [fullSatSearch verbose bsa, simpleSatSearch verbose bsa]
  case out of
    Nothing -> error "Assertion: At the full search always returns Just (...)"
    Just b -> return b
-----------------------------------------------------------------------------
