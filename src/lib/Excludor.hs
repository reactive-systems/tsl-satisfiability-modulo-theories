-----------------------------------------------------------------------------
-- |
-- Module      :  Excludor
-- Maintainer  :  Philippe Heim
--
-- This module contains an implementation of the exclusion data structure
-- used by the algorithm. This includes:
-- - An on-the-fly generation of an safety automaton for excluding sub-words
-- - An representation of Non-deterministic Büchi Automata with respective
--   emptiness checks
--
-----------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

module Excludor
  ( Exclude
  , possible
  , exclude
  , fromBSA
  , Excludor.size
  ) where

-----------------------------------------------------------------------------
import Data.Set as Set
  ( Set
  , empty
  , filter
  , fromList
  , insert
  , map
  , singleton
  , size
  , toList
  , union
  , unions
  )

import Data.Map as Map (lookup)

import BuechiStreamAutomaton as BSA
  ( BSA
  , ExplTrans
  , accepting
  , initial
  , relation
  , transitionLabels
  )

-----------------------------------------------------------------------------
--
-- The sub-word exclusion automaton
--
-----------------------------------------------------------------------------
-- | 'ExAutState' represents a set of the on-the-fly generated 
-- safety automata for excluding sub-words
--
newtype ExAutState ap =
  ExAutState (Set [ap])
  deriving (Eq, Ord, Show)

-----------------------------------------------------------------------------
-- | 'startExAutState' is the initial state of an excluding-safety-automaton
--
startExAutState :: Ord ap => ExAutState ap
startExAutState = ExAutState empty

-----------------------------------------------------------------------------
-- | 'deadEnd' checks if and 'ExAutState' represents a safety violation
--
deadEnd :: Ord ap => ExAutState ap -> Bool
deadEnd (ExAutState prefixes) = [] `elem` prefixes

-----------------------------------------------------------------------------
-- | 'next' computes the successor of an 'ExAutState' and the read symbol
-- under a set of sub-words that are to be excluded 
-- 
next :: Ord ap => Set [ap] -> ExAutState ap -> ap -> ExAutState ap
next excludedWords (ExAutState prefixes) ap =
  let newPotentialPrefixes = toList $ prefixes `union` excludedWords
      newPrefixes = fromList $ concatMap (applyFirst ap) newPotentialPrefixes
   in ExAutState newPrefixes
  where
    applyFirst :: Eq ap => ap -> [ap] -> [[ap]]
    applyFirst _ [] = [[]] -- Do NOT remove bad prefixes to preserve bad states
    applyFirst y (x:xr) = [xr | x == y]

-----------------------------------------------------------------------------
-- | 'excludes' check is a word is excluded by a set of forbidden sub-words
-- (i.e. if the word has a sub-word which is inside the set of forbidden
-- sub-words) using the excluding-safety-automaton
--
excludes :: Ord ap => Set [ap] -> [ap] -> Bool
excludes excludedWords word = deadEnd (run startExAutState word)
  where
    run st [] = st
    run st (x:xr) = run (next excludedWords st x) xr

-----------------------------------------------------------------------------
--
-- Non-deterministic Büchi Automata
--
-----------------------------------------------------------------------------
-- | 'State' represents the state of an 'NBA'
--
data State ap
  = ISt Int
  -- ^ 'ISt' is an atomic state (simply an Integer)
  | ASt (State ap, ExAutState ap)
  -- ^ 'ASt' is a stated "crossed" with an excluding state
  deriving (Eq, Ord, Show)

-----------------------------------------------------------------------------
-- | 'NBA' is the interface for non-deterministic Büchi automata. Note that
-- the implementation does not necessarily requires a pre-computed data
-- structure but also allows an on-the-fly computation
--
data NBA ap =
  NBA
    { atomicProps :: Set ap
      -- ^ 'atomicProps' are the atomic propositions the NBA
    , trans :: State ap -> ap -> Set (State ap)
      -- ^ 'trans' represents the transition relation. Since this is a 
      -- function it might be computed dynamically
    , inititials :: Set (State ap)
      -- ^ 'inititials' is the set of initial states
    , accept :: State ap -> Bool
      -- ^ 'accept' checks whether some state is an accept one
    }

-----------------------------------------------------------------------------
-- | 'postAP' computes the successor 'State's of a set of 'State's after
-- reading some atomic proposition
--
postAP :: Ord ap => NBA ap -> Set (State ap) -> ap -> Set (State ap)
postAP NBA {trans = trans} sts ap = unions [trans s ap | s <- toList sts]

-----------------------------------------------------------------------------
-- | 'post' computes the possible successor 'State's of a set of 'State's 
--
post :: Ord ap => NBA ap -> Set (State ap) -> Set (State ap)
post nba@NBA {atomicProps = aps} sts =
  unions [postAP nba sts ap | ap <- toList aps]

-----------------------------------------------------------------------------
-- | 'runPrefix' computes the reachable 'State's of an 'NBA' after reading
-- some prefix
--
runPrefix :: Ord ap => NBA ap -> [ap] -> Set (State ap)
runPrefix nba@NBA {inititials = inititials} word = runPrefix' word inititials
  where
    runPrefix' [] sts = sts
    runPrefix' (x:xr) sts = runPrefix' xr (postAP nba sts x)

-----------------------------------------------------------------------------
-- | 'reachablesFrom' computes the set of 'State's that is reachable from
-- a given one in an 'NBA' using breath-first-search
-- 
reachablesFrom :: Ord ap => NBA ap -> Set (State ap) -> Set (State ap)
reachablesFrom nba states = bfs (toList states) states
  where
    bfs [] sts = sts
    bfs (x:xr) sts =
      bfs
        (xr ++ [s | s <- toList $ post nba (singleton x), s `notElem` sts])
        (post nba (singleton x) `union` sts)

-----------------------------------------------------------------------------
-- | 'isReachable' checks if some 'State' is reachable from a given set of
-- 'State's within an 'NBA' using breath-first search
--
isReachable :: Ord ap => NBA ap -> State ap -> Set (State ap) -> Bool
isReachable nba state states = bfs (toList states) states
  where
    bfs [] sts = state `elem` sts
    bfs (x:xr) sts =
      state == x ||
      bfs
        (xr ++ [s | s <- toList $ post nba (singleton x), s `notElem` sts])
        (post nba (singleton x) `union` sts)

-----------------------------------------------------------------------------
-- | 'emptyFrom' checks if an 'NBA' is empty if starting form a specific
-- set of 'State's (i.e. an alternate set of initial states)
--
emptyFrom :: Ord ap => NBA ap -> Set (State ap) -> Bool
emptyFrom nba sts =
  let reachAcc = Set.filter (accept nba) (reachablesFrom nba sts)
      check s = isReachable nba s (post nba (singleton s))
   in not (any check reachAcc)

-----------------------------------------------------------------------------
-- | 'emptyAfter' checks if an NBA is empty after reading some prefix
-- (i.e empty starting from the states reachable after reading the prefix)
--
emptyAfter :: Ord ap => NBA ap -> [ap] -> Bool
emptyAfter nba word = emptyFrom nba (runPrefix nba word)

-----------------------------------------------------------------------------
-- | 'excludeFromNBA' removes all words from an 'NBA' that have a sub-word
-- inside the set of forbidden sub-words.  This is done by performing a
-- direct product with the sub-word exclusion safety automata. 
--
excludeFromNBA :: Ord ap => Set [ap] -> NBA ap -> NBA ap
excludeFromNBA excludeWords nba =
  NBA
    { atomicProps = atomicProps nba
    , trans =
        \st ap ->
          case st of
            ASt (nbaState, extState) ->
              if deadEnd extState
                then empty
                else let newExclState = next excludeWords extState ap
                      in Set.map
                           (\newNBAState -> ASt (newNBAState, newExclState))
                           (trans nba nbaState ap)
            _ ->
              error "Assertion: Invariant violated - this should never happen"
    , inititials = Set.map (\s -> ASt (s, startExAutState)) (inititials nba)
    , accept =
        \case
          ASt (nbaState, extState) ->
            accept nba nbaState && not (deadEnd extState)
          _ -> error "Assertion: Invariant violated - this should never happen"
    }

-----------------------------------------------------------------------------
--
-- The exclusion data structure
--
-----------------------------------------------------------------------------
-- | 'Exclude' represents an exclusion data structure. The implementation 
-- is as follows: The 'BSA' to be reduced is an 'NBA' over its transitions.
-- Furthermore the 'Exclude' structure holds the set of words to 'exclude'
-- explicitly.
--
data Exclude ap =
  Exclude (NBA ap) (Set [ap])

-----------------------------------------------------------------------------
-- | The 'size' of an 'Exclude' is the number of excluded words
--
size :: Ord a => Exclude a -> Int
size (Exclude _ exs) = Set.size exs

-----------------------------------------------------------------------------
-- | 'possible' checks if some finite prefix is still possible withing the 
-- limitations of an exclusion, i.e. if there is some word that is
-- not excluded and has this prefix. This is done by computing the
-- cross-product of the NBA and the sub-word excluding safety automation
-- on-the-fly an doing an emptiness check
--
possible :: Ord a => Exclude a -> [a] -> Bool
possible (Exclude nba excludeSet) word =
  not (excludeSet `excludes` word) && -- Speedup: Trivial excluded words
  not (emptyAfter (excludeFromNBA excludeSet nba) word)

-----------------------------------------------------------------------------
-- | 'excludes' excludes a forbidden sub-word
--
exclude :: Ord a => Exclude a -> [a] -> Exclude a
exclude e@(Exclude nba excludeSet) word =
  if excludeSet `excludes` word
    then e -- if the word is already excluded there is no need to redo it
    else Exclude nba (word `insert` excludeSet)

-----------------------------------------------------------------------------
-- | 'fromBSA' computes an 'Exclude' that only allows words over transitions 
-- of the 'BSA' that are possible within in the 'BSA' ignoring the 
-- predicate constraints (i.e. interpret transition as atomic propositions)
--
fromBSA :: (Ord c, Ord f, Ord p) => BSA c f p -> Exclude ExplTrans
fromBSA bsa = Exclude nba empty
  where
    nba =
      NBA
        { atomicProps = transitionLabels bsa
        , trans =
            \case
              ISt q ->
                \l ->
                  case Map.lookup q (relation bsa) of
                    Nothing -> empty
                    Just m' ->
                      case Map.lookup l m' of
                        Nothing -> empty
                        Just q' -> Set.map ISt q'
              _ -> error "Assertion: This should not happen"
        , inititials = Set.map ISt $ BSA.initial bsa
        , accept = \st -> st `elem` Set.map ISt (accepting bsa)
        }
-----------------------------------------------------------------------------
