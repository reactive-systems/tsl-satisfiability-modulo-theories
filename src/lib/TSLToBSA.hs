-----------------------------------------------------------------------------
-- |
-- Module      :  TSLToBSA
-- Maintainer  :  Philippe Heim
--
-- This module implements the transformation of a TSL specification into
-- a BSA. This includes the following steps:
--
-- 1. Approximating the TSL specification with a LTL formula (using tsltools)
-- 2. Computing a respective NBA (using spot and syfco)
-- 3. Parsing of the NBA in the HOA format (custom parser)
-- 4. Transforming the HOA into an BSA by paring the tsltools atomic
--    proposition encoding 
--
-----------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-----------------------------------------------------------------------------
module TSLToBSA
  ( toBSA
  , spotLTL2NBA
  ) where

-----------------------------------------------------------------------------
import Data.List (drop, find, findIndex, isPrefixOf, replicate)
import Data.Map as Map (empty)
import Data.Set as Set (empty, fromList, map, singleton, toList, unions)

import BuechiStreamAutomaton
  ( BSA(..)
  , Conj
  , DNF
  , Label
  , Literal(..)
  , defaultFlags
  , dnfElems
  , updateExplicit
  )
import Terms

import Syfco
  ( Configuration(outputFormat)
  , WriteFormat(WRING)
  , apply
  , defaultCfg
  , fromTLSF
  )
import TSL
  ( FunctionTerm(..)
  , PredicateTerm(..)
  , SignalTerm(..)
  , Specification
  , decodeInputAP
  , decodeOutputAP
  , toTLSF
  )

import ExternalCall (runCMD)
import System.IO (hFlush, stdout)

-----------------------------------------------------------------------------
-- | 'spotTimeout' is the timeout used for spot optimizations in seconds
--
spotTimeout :: Int
spotTimeout = 20

-----------------------------------------------------------------------------
-- | 'spotLTL2NBA' calls spot to transform a LTL formula into a 
-- non-determinstic Büchi automaton in HOA format
--
spotLTL2NBA :: String -> IO String
spotLTL2NBA ltl = do
  (hoa, err, _) <-
    runCMD ("timeout -v " ++ show spotTimeout ++ " ltl2tgba -B -") ltl
  if err == ""
    then do
      putStrLn "SPOT FINISHED"
      hFlush stdout
      return hoa
    else do
      putStrLn "SPOT-TO"
      hFlush stdout
      (hoa', _, _) <- runCMD "ltl2tgba --low -B -" ltl
      return hoa'

-----------------------------------------------------------------------------
-- | 'toBSA' converts a 'Specification' into a 'BSA' given a transformation
-- from a LTL formula to an HOA in String form
--
toBSA ::
     (String -> IO String)
  -> Specification
  -> IO (Either String (BSA String String String))
toBSA transform spec =
  case fromTLSF (toTLSF "TSL-Sat temporary spec" spec) of
    Left error -> return (Left (show error))
    Right spec ->
      case apply (defaultCfg {outputFormat = WRING}) spec of
        Left error -> return (Left (show error))
        Right wringSpec -> do
          strHOA <- transform wringSpec
          let hoa = parseHOA strHOA
          return (Right (hoa2bsa hoa))

-----------------------------------------------------------------------------
--
-- Internal 'HOA' representation with a custom parser
--
-- TODO: Switch to HOA Library, since the parser is pretty broken 
-- (i.e. only works for multi-lines and so on)
--
-----------------------------------------------------------------------------
-- | 'HOA' is the internal representation of the parsed Hanoi Automaton
--
data HOA =
  HOA
    { start :: Int
      -- ^ 'start' is the initial state as position in the state list
    , state :: [(Bool, [(DNF String, Int)])]
      -- ^ 'state' is the list of states with acceptance and their transitions
    }
  deriving (Show)

-----------------------------------------------------------------------------
-- | 'prepAPs' parses a list of atomic propositions
--
prepAPs :: String -> [String]
prepAPs = getEscapedOut
  where
    getEscapedOut =
      \case
        [] -> []
        '\"':xr -> getEscapedIn [] xr
        _:xr -> getEscapedOut xr
    getEscapedIn acc =
      \case
        [] -> [reverse acc]
        '\"':xr -> reverse acc : getEscapedOut xr
        x:xr -> getEscapedIn (x : acc) xr

-----------------------------------------------------------------------------
-- | 'parseHOATrans' parses a transition of a 'HOA'
--
parseHOATrans :: [String] -> String -> (DNF String, Int)
parseHOATrans aps trans =
  case split trans (== ']') of
    ['[':f, ' ':q] -> (parseForm aps (filter (/= ' ') f), read q)
    _ -> error $ "HOA: Found " ++ trans ++ " while parsing transition"

-----------------------------------------------------------------------------
-- | 'parseForm' parses a 'DNF' formula on 'HOA' transitions
--
parseForm :: [String] -> String -> DNF String
parseForm aps =
  \case
    "t" -> [[]]
    str -> parseConj aps <$> split str (== '|')

-----------------------------------------------------------------------------
-- | 'parseConj' parses a conjunctive sub-formula on 'HOA' transitions
--
parseConj :: [String] -> String -> Conj String
parseConj aps str = parseLiteral aps <$> split str (== '&')

-----------------------------------------------------------------------------
-- | 'parseLiteral' parses 'Literal's of 'HOA' transitions
--
parseLiteral :: [String] -> String -> Literal String
parseLiteral aps =
  \case
    '!':num -> Neg $ aps !! read num
    num -> Pos $ aps !! read num

-----------------------------------------------------------------------------
-- | 'parseHOAState' parses the declaration of a state inside the 'HOA' body
--
parseHOAState :: String -> (Int, Bool)
parseHOAState str =
  case split str (== ' ') of
    [_, q] -> (read q, False)
    [_, q, "{0}"] -> (read q, True)
    xs -> error $ "HOA: Found " ++ show xs ++ " while parsing state"

-----------------------------------------------------------------------------
-- | 'parseHOABody' parses the body of a 'HOA'
--
parseHOABody :: [String] -> HOA -> [String] -> HOA
parseHOABody aps hoa = parseHOALine' True hoa 0 False []
  where
    parseHOALine' ::
         Bool -> HOA -> Int -> Bool -> [(DNF String, Int)] -> [String] -> HOA
    parseHOALine' init hoa q acc trans = prsLn
      where
        prsLn [] = updatedHOA
        prsLn (x:xr)
          | "State: " `isPrefixOf` x =
            let (q', acc') = parseHOAState x
             in parseHOALine' False updatedHOA q' acc' [] xr
          | "--END--" `isPrefixOf` x = updatedHOA
          | otherwise =
            parseHOALine' init hoa q acc (parseHOATrans aps x : trans) xr
        --
        updatedHOA =
          if init
            then hoa
            else hoa {state = update (state hoa) (acc, trans) q}

-----------------------------------------------------------------------------
-- | 'parseHOA' converts an Hanoi automaton with Büchi acceptance into 
-- the internal format
--
parseHOA :: String -> HOA
parseHOA hoa =
  let lines = split hoa (== '\n')
      aps =
        case find (isPrefixOf "AP: ") lines of
          Just apsStr -> prepAPs apsStr
          Nothing -> error "HOA: Atomic Propositions not found"
      stateNum =
        case find (isPrefixOf "States: ") lines of
          Just apLine -> read $ drop 8 apLine
          Nothing -> error "HOA: State number not found" :: Int
      startState =
        case find (isPrefixOf "Start: ") lines of
          Just apLine -> read $ drop 7 apLine
          Nothing -> error "HOA: Initial state not found" :: Int
      unparsedHOA =
        HOA {start = startState, state = replicate stateNum (False, [])}
      body =
        case findIndex (isPrefixOf "--BODY--") lines of
          Just n -> drop (n + 1) lines
          Nothing -> error "HOA: Body not found"
   in parseHOABody aps unparsedHOA body

-----------------------------------------------------------------------------
-- | 'split' is a helper function which splits the list at each point some
-- predicate is fulfilled (removing the respective element)
--
split :: [a] -> (a -> Bool) -> [[a]]
split xs p = split' [] xs
  where
    split' acc [] = [reverse acc]
    split' acc (x:xr) =
      if p x
        then reverse acc : split' [] xr
        else split' (x : acc) xr

-----------------------------------------------------------------------------
-- | 'update' updates an element inside of a list
-- TODO: This should normally already exist
--
update :: [a] -> a -> Int -> [a]
update [] _ _ = error "List UPDATE: Index does not exists"
update (x:xr) a n =
  if n <= 0
    then a : xr
    else x : update xr a (n - 1)

-----------------------------------------------------------------------------
--
-- Converting the internal 'HOA' format into a 'BSA'
--
-----------------------------------------------------------------------------
-- | 'convertFunctionTerm' converts a 'SignalTerm' used by tsltools into 
-- the internal representation of a 'FunctionTerm'
-- 
convertFunctionTerm :: SignalTerm String -> Terms.FunctionTerm String String
convertFunctionTerm =
  \case
    Signal c -> Cell c
    FunctionTerm ft ->
      let (name, arguments) = functionTermUncurry ft
       in Func name (fmap convertFunctionTerm arguments)
    PredicateTerm _ ->
      error "Assertion: A function term should not contain predicates"
  where
    functionTermUncurry ::
         TSL.FunctionTerm String -> (String, [SignalTerm String])
    functionTermUncurry =
      \case
        FunctionSymbol name -> (name, [])
        FApplied ft arg ->
          let (name, restArgs) = functionTermUncurry ft
           in (name, restArgs ++ [arg])

-----------------------------------------------------------------------------
-- | 'convertPredicateTerm' converts a 'PredicateTerm' used by tsltools into 
-- the internal representation of a 'PredicateTerm'
-- 
convertPredicateTerm ::
     TSL.PredicateTerm String -> Terms.PredicateTerm String String String
convertPredicateTerm pt =
  let (name, arguments) = predicateTermUncurry pt
   in Pred name (fmap convertFunctionTerm arguments)
  where
    predicateTermUncurry ::
         TSL.PredicateTerm String -> (String, [SignalTerm String])
    predicateTermUncurry =
      \case
        BooleanTrue -> error "Boolean constants are not supporte yet"
        BooleanFalse -> error "Boolean constants are not supporte yet"
        BooleanInput _ -> error "Boolean inputs are not supported yet"
        PredicateSymbol name -> (name, [])
        PApplied ft arg ->
          let (name, restArgs) = predicateTermUncurry ft
           in (name, restArgs ++ [arg])

-----------------------------------------------------------------------------
-- | 'ap2term' parses a TLSF encoded 'Label'. 
--
ap2term :: String -> Label String String String
ap2term ap =
  case decodeInputAP ap of
    Right st -> Left (convertPredicateTerm st)
    Left _ ->
      case decodeOutputAP ap of
        Right (cell, ft) -> Right (cell, convertFunctionTerm ft)
        Left _ ->
          error
            "Error: tsltools could not decode its encoding; something is broken there"

-----------------------------------------------------------------------------
-- | 'hoa2bsa' converts the internal 'HOA' format into a 'BSA'
--
hoa2bsa :: HOA -> BSA String String String
hoa2bsa hoa =
  updateExplicit $
  BSA
    { stateNum = length $ state hoa
    , initial = singleton (start hoa)
    , accepting = fromList $ fmap snd $ filter (fst . fst) $ numPos (state hoa)
    , cells = cells
    , guards = guards
    , updates = updates
    , trans = newTrans
    , relation = Map.empty
    , label = const undefined
    , flags = defaultFlags
    }
  where
    symTrans =
      toList $
      unions [Set.map fst (newTrans s) | s <- [0 .. length (state hoa) - 1]]
    --
    elems = toList $ unions (fmap dnfElems symTrans)
    --
    cells =
      unions $
      fmap
        (\case
           Left pt -> getCellsP pt
           Right (c, ft) -> unions [singleton c, getCellsF ft])
        elems
    --
    guards =
      unions $
      fmap
        (\case
           Left pt -> singleton pt
           Right _ -> Set.empty)
        elems
    -- 
    updates =
      unions $
      [singleton (c, Cell c) | c <- toList cells] ++
      fmap
        (\case
           Left _ -> Set.empty
           Right u -> singleton u)
        elems
    --
    newTrans q =
      fromList $
      fmap
        (\(f, q) ->
           ( fmap
               (fmap
                  (\case
                     Pos str -> Pos $ ap2term str
                     Neg str -> Neg $ ap2term str))
               f
           , q))
        (snd (state hoa !! q))
    --
    numPos :: [a] -> [(a, Int)]
    numPos xs = numPos' xs 0 []
      where
        numPos' [] _ acc = reverse acc
        numPos' (x:xr) n acc = numPos' xr (n + 1) ((x, n) : acc)
-----------------------------------------------------------------------------
