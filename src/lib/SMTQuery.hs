-----------------------------------------------------------------------------
-- |
-- Module      :  SMTQuery
-- Maintainer  :  Philippe Heim 
--
-- This module provides an interface to create SMT queries as needed by
-- the algorithm and a call interface to the Z3 SMT solver. 
--
-----------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-----------------------------------------------------------------------------
module SMTQuery
  ( SMTForm(..)
  , SMTQuery
  , anySMTSat
  ) where

-----------------------------------------------------------------------------
import Data.Set (Set, empty, toList, unions)
import ExternalCall (runCMD)
import Text.Read (readMaybe)

import Terms
  ( FunctionTerm(..)
  , PredicateTerm(..)
  , getFunctionsF
  , getFunctionsP
  , getPredicates
  )

-----------------------------------------------------------------------------
-- | 'SMTForm' represents the three type of SMT assertions that are used in
-- the algorithm
--
data SMTForm c f p
  = PPred (PredicateTerm c f p)
  -- ^ This represents that a predicate should be true
  | NPred (PredicateTerm c f p)
  -- ^ This represents that a predicate should be false
  | Eqc (c -> FunctionTerm c f) (c -> FunctionTerm c f) -- 
  -- ^ This represents that two assignments of cells to function terms 
  -- should be equal

-----------------------------------------------------------------------------
-- | 'SMTQuery' is simply a list of assertions represented by 'SMTForm'
--
type SMTQuery c f p = [SMTForm c f p]

-----------------------------------------------------------------------------
-- | 'getFunctions' returns all function symbols of an 'SMTForm' with
-- their respective arity
--
getFunctions :: Ord f => [c] -> SMTForm c f p -> Set (f, Int)
getFunctions cells =
  \case
    PPred pt -> getFunctionsP pt
    NPred pt -> getFunctionsP pt
    Eqc f g ->
      unions $
      [getFunctionsF (f c) | c <- cells] ++ [getFunctionsF (g c) | c <- cells]

-----------------------------------------------------------------------------
-- | 'getQueryFunctions' lifts 'getFunctions' to an 'SMTQuery'
--
getQueryFunctions :: Ord f => [c] -> SMTQuery c f p -> Set (f, Int)
getQueryFunctions cells xs = unions $ fmap (getFunctions cells) xs

-----------------------------------------------------------------------------
-- | 'getPredicates' returns all predicate symbols of an 'SMTForm' with
-- their respective arity
--
getPredicates :: Ord p => SMTForm c f p -> Set (p, Int)
getPredicates =
  \case
    PPred pt -> Terms.getPredicates pt
    NPred pt -> Terms.getPredicates pt
    _ -> empty

-----------------------------------------------------------------------------
-- | 'getQueryPredicates' lifts 'getPredicates' to an 'SMTQuery'
--
getQueryPredicates :: Ord p => SMTQuery c f p -> Set (p, Int)
getQueryPredicates xs = unions $ fmap SMTQuery.getPredicates xs

-----------------------------------------------------------------------------
-- | 'filterKeywords' filters functions and predicate names for special 
-- one like equality and replaces them respectively. 
--
-- TODO: This should probably by integrated somehow into tsltools and
-- handled with a type system. However, for now this is an appropriate
-- workaround.
--
filterKeywords :: String -> Maybe String
filterKeywords =
  \case
    "equal" -> Just "="
    "_leq" -> Just "<="
    "_lt" -> Just "<"
    "_geq" -> Just ">="
    "_gt" -> Just ">"
    "_add" -> Just "+"
    "_sub" -> Just "-"
    '_':'c':n ->
      case readMaybe n :: Maybe Int of
        Just num -> Just (show num)
        Nothing -> Nothing
    _ -> Nothing

-----------------------------------------------------------------------------
-- | 'funcTermToSMTLib2' transforms a 'FunctionTerm' into a string given some 
-- naming functions for the functions and cells
--
funcTermToSMTLib2 ::
     (c -> String) -> (f -> String) -> FunctionTerm c f -> String
funcTermToSMTLib2 cts fts =
  \case
    Cell c -> " x" ++ cts c ++ " "
    Func f [] ->
      case filterKeywords (fts f) of
        Nothing -> " f" ++ fts f ++ " "
        Just s -> " " ++ s ++ " "
    Func f xs ->
      case filterKeywords (fts f) of
        Nothing ->
          "(f" ++ fts f ++ concatMap (funcTermToSMTLib2 cts fts) xs ++ ")"
        Just s ->
          "(" ++ s ++ " " ++ concatMap (funcTermToSMTLib2 cts fts) xs ++ ")"

-----------------------------------------------------------------------------
-- | 'predTermToSMTLib2' transforms a 'PredicateTerm' into a string given some 
-- naming functions for the predicates, functions, and cells
--
predTermToSMTLib2 ::
     (c -> String)
  -> (f -> String)
  -> (p -> String)
  -> PredicateTerm c f p
  -> String
predTermToSMTLib2 cts fts pts =
  \case
    Pred p xs ->
      case filterKeywords (pts p) of
        Nothing ->
          "(p" ++ pts p ++ concatMap (funcTermToSMTLib2 cts fts) xs ++ ")"
        Just s ->
          "(" ++ s ++ " " ++ concatMap (funcTermToSMTLib2 cts fts) xs ++ ")"

-----------------------------------------------------------------------------
-- | 'smtFormToSMTLib2' transforms an 'SMTForm' assertion into a string
-- given naming functions and the list of all available cells
--
smtFormToSMTLib2 ::
     (c -> String)
  -> (f -> String)
  -> (p -> String)
  -> [c]
  -> SMTForm c f p
  -> String
smtFormToSMTLib2 cts fts pts cells =
  \case
    PPred pt -> "(assert " ++ predTermToSMTLib2 cts fts pts pt ++ ")\n"
    NPred pt -> "(assert (not " ++ predTermToSMTLib2 cts fts pts pt ++ "))\n"
    Eqc f g -> concat [assertEq (f c) (g c) | c <- cells]
  where
    assertEq t1 t2 =
      "(assert (= " ++
      funcTermToSMTLib2 cts fts t1 ++ funcTermToSMTLib2 cts fts t2 ++ "))\n"

-----------------------------------------------------------------------------
-- | 'declareCell' creates the declaration for a cell (the initial value)
--
declareCell :: (c -> String) -> c -> String
declareCell cts c =
  case cts c
    -- TODO: The first case is in continuation with the workaround 
    -- provided by 'filterKeywords'
        of
    'i':'n':'t':'_':_ -> "(declare-const x" ++ cts c ++ " Int)\n"
    _ -> "(declare-const x" ++ cts c ++ " A)\n"

-----------------------------------------------------------------------------
-- | 'aritySort' is a helper function generating parts of the type structure
-- for uninterpreted functions
-- 
aritySort :: Int -> String
aritySort n
  | n == 1 = "A"
  | n > 1 = "A " ++ aritySort (n - 1)
  | otherwise = ""

-----------------------------------------------------------------------------
-- | 'declareFunction' declares an uninterpreted function for an SMTLib2
-- query
--
declareFunction :: (f -> String) -> (f, Int) -> String
declareFunction fts (f, n) =
  "(declare-fun f" ++ fts f ++ " (" ++ aritySort n ++ ") A)\n"

-----------------------------------------------------------------------------
-- | 'declarePredicate' declares an uninterpreted predicate for an SMTLib2
-- query (as an uninterpreted predicate)
--
declarePredicate :: (p -> String) -> (p, Int) -> String
declarePredicate pts (p, n) =
  "(declare-fun p" ++ pts p ++ " (" ++ aritySort n ++ ") Bool)\n"

-----------------------------------------------------------------------------
-- | 'smtQueryToSMTLib2' generates a full SMTLib2 'String' query out of
-- a 'SMTQuery' given all cells and naming functions
--
smtQueryToSMTLib2 ::
     (Ord c, Ord f, Ord p)
  => (c -> String)
  -> (f -> String)
  -> (p -> String)
  -> [c]
  -> SMTQuery c f p
  -> String
smtQueryToSMTLib2 cts fts pts cells query =
  let functions = toList $ getQueryFunctions cells query
      predicates = toList $ getQueryPredicates query
   in "(declare-sort A)\n" ++
      concatMap (declareCell cts) cells ++
      concatMap (declareFunction fts) functions ++
      concatMap (declarePredicate pts) predicates ++
      concatMap (smtFormToSMTLib2 cts fts pts cells) query ++ "(check-sat)"

-----------------------------------------------------------------------------
-- | 'queryZ3' calls Z3 given a SMTLib2 Query as a 'String'
--
queryZ3 :: String -> IO Bool
queryZ3 form = do
  (out, _, _) <- runCMD "z3 -smt2 -in" form
  case out of
    "sat\n" -> return True
    "sat" -> return True
    "unsat\n" -> return False
    "unsat" -> return False
    _ -> error "Assertion: Z3 did not output sat/unsat"

-----------------------------------------------------------------------------
-- | 'anySMTSat' checks if any of a given 'SMTQuery' over 'String's is 
-- satisfiable
--
anySMTSat :: [String] -> [SMTQuery String String String] -> IO Bool
anySMTSat cells =
  \case
    [] -> return False
    q:qr -> do
      isSat <- queryZ3 $ smtQueryToSMTLib2 id id id cells q
      if isSat
        then return True
        else anySMTSat cells qr
-----------------------------------------------------------------------------
