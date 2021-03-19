-----------------------------------------------------------------------------
-- |
-- Module      :  Terms
-- Maintainer  :  Philippe Heim 
--
-- This module implements the internal representation of terms and some 
-- access methods (e.g. for some sub-symbols).
--
-----------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-----------------------------------------------------------------------------
module Terms
  ( FunctionTerm(..)
  , PredicateTerm(..)
  , substF
  , substP
  , getCellsF
  , getCellsP
  , getFunctionsF
  , getFunctionsP
  , getPredicates
  , funcTermToString
  , predTermToString
  ) where

-----------------------------------------------------------------------------
import Data.Set (Set, empty, singleton, unions)

-----------------------------------------------------------------------------
-- | 'FunctionTerm' represents a function term
--
data FunctionTerm c f
  = Cell c
  -- ^ 'Cell' represents a cell of a function term
  | Func f [FunctionTerm c f]
  -- ^ 'Func' represents a function application
  deriving (Eq, Ord, Show)

-----------------------------------------------------------------------------
-- | 'PredicateTerm' represents a predicate term
--
data PredicateTerm c f p =
  Pred p [FunctionTerm c f]
  -- ^ 'Pred' represent a predicate application
  deriving (Eq, Ord, Show)

-----------------------------------------------------------------------------
-- | 'funcTermToString' is pretty-printing method for 'FunctionTerm's
--
funcTermToString :: (Show c, Show f) => FunctionTerm c f -> String
funcTermToString =
  \case
    Cell c -> show c
    Func f st ->
      "(" ++ show f ++ concatMap (\ft -> " " ++ funcTermToString ft) st ++ ")"

-----------------------------------------------------------------------------
-- | 'predTermToString' is pretty-printing method for 'PredicateTerm's
--
predTermToString :: (Show c, Show f, Show p) => PredicateTerm c f p -> String
predTermToString (Pred p st) =
  show p ++ concatMap (\ft -> " " ++ funcTermToString ft) st

-----------------------------------------------------------------------------
-- | 'substF' substitutes the cells of a 'FunctionTerm' by another 
-- 'FunctionTerm'
--
substF :: (c -> FunctionTerm c f) -> FunctionTerm c f -> FunctionTerm c f
substF sub =
  \case
    Cell c -> sub c
    Func f st -> Func f (fmap (substF sub) st)

-----------------------------------------------------------------------------
-- | 'substF' substitutes the cells of a 'PredicateTerm' by a 'FunctionTerm'
--
substP :: (c -> FunctionTerm c f) -> PredicateTerm c f p -> PredicateTerm c f p
substP sub (Pred p subT) = Pred p (fmap (substF sub) subT)

-----------------------------------------------------------------------------
-- | 'getCellsF' extract all cells of a 'FunctionTerm'
--
getCellsF :: Ord c => FunctionTerm c f -> Set c
getCellsF =
  \case
    Cell c -> singleton c
    Func _ xs -> unions (fmap getCellsF xs)

-----------------------------------------------------------------------------
-- | 'getCellsP' extract all cells of a 'PredicateTerm'
--
getCellsP :: Ord c => PredicateTerm c f p -> Set c
getCellsP (Pred _ xs) = unions (fmap getCellsF xs)

-----------------------------------------------------------------------------
-- | 'getFunctionsF' extract all function symbols with their respective
-- arity from a 'FunctionTerm'
--
getFunctionsF :: Ord f => FunctionTerm c f -> Set (f, Int)
getFunctionsF =
  \case
    Cell _ -> empty
    Func f xs -> unions $ singleton (f, length xs) : fmap getFunctionsF xs

-----------------------------------------------------------------------------
-- | 'getFunctionsP' extract all function symbols with their respective
-- arity from a 'PredicateTerm'
--
getFunctionsP :: Ord f => PredicateTerm c f p -> Set (f, Int)
getFunctionsP (Pred _ xs) = unions (fmap getFunctionsF xs)

-----------------------------------------------------------------------------
-- | 'getPredicates' extract all predicate symbols with their respective
-- arity from a 'PredicateTerm'
--
getPredicates :: Ord p => PredicateTerm c f p -> Set (p, Int)
getPredicates (Pred p xs) = singleton (p, length xs)
-----------------------------------------------------------------------------
