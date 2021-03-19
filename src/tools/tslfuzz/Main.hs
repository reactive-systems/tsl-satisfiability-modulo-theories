-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Maintainer  :  Philippe Heim 
--
-- The main module of the callable fuzzer tool base on spots
-- 'randltl'.
--
-- GENERAL REMARK: This tools does what it should but is 
-- implementation-wise quite ugly and not very flexible. For the moment
-- I left it so, to document how the benchmarks where generated 
-- (since there have benn improvments over time). But on the long run
-- this should be rewritten (and maybe replace by QuickCheck or so)
--
-----------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-----------------------------------------------------------------------------
module Main where

-----------------------------------------------------------------------------
import Control.Monad (replicateM)
import Data.List as List (isPrefixOf)
import ExternalCall (runCMD)
import System.Random as Random (randomIO)
import TSLSat
  ( FunctionTerm(..)
  , PredicateTerm(..)
  , funcTermToString
  , predTermToString
  )

import System.Directory (doesDirectoryExist)
import System.Environment (getArgs)
import Text.Read (readMaybe)

-----------------------------------------------------------------------------
-- | 'findAndReplace' finds a substring inside of a string an replaces it
-- by another one
--
findAndReplace :: String -> String -> String -> String
findAndReplace [] _ = id
findAndReplace old new =
  \case
    [] -> []
    s:sr ->
      if old `isPrefixOf` (s : sr)
        then new ++ findAndReplace old new (drop (length old) (s : sr))
        else s : findAndReplace old new sr

-----------------------------------------------------------------------------
-- | 'genRandLTL' uses randltl (spot) to generate a LTL formula and 
-- respective atomic propostions given the size, a seed an a number of
-- atomic propositions
--
genRandLTL :: Int -> Int -> Int -> IO (String, [String])
genRandLTL size seed apCount
        --
 =
  let multZero :: Int -> String
      multZero n =
        if n <= 0
          then ""
          else "2" ++ multZero (n - 1)
        --
      num2ap :: Int -> String
      num2ap n = "ap" ++ multZero n ++ "pa"
        --
      aps = [num2ap n | n <- [1 .. apCount]]
        --
      randLTLQuery =
        "randltl -p  --tree-size=" ++
        show size ++
        " --ltl-priorities='xor=0, M=0, false=0, true=0' --seed=" ++
        show seed ++ concatMap (" " ++) aps
   in do (out, _, _) <- runCMD randLTLQuery ""
         let ltl =
               findAndReplace "1" "true" $
               findAndReplace "0" "false" $
               findAndReplace "|" "||" $ findAndReplace "&" "&&" out
         return (ltl, aps)

-----------------------------------------------------------------------------
-- | 'genRandCells' generates up to 3 random cells
--
genRandCells :: IO [String]
genRandCells = do
  n <- randomIO
  return $ genCells (n `mod` 3)
  where
    genCells :: Int -> [String]
    genCells n =
      if n < 0
        then []
        else ("x" ++ show n) : genCells (n - 1)

-----------------------------------------------------------------------------
-- | 'genRandFuncTerm' generates a random function term with depth up to 2
-- and arity up to 2
--
genRandFuncTerm :: [String] -> IO (FunctionTerm String String)
genRandFuncTerm cells = do
  m <- randomIO
  let depth = m `mod` 2
  c <- randomIO
  randList <- replicateM (depth * 4) randomIO
  return $ genFuncTerm randList c
  where
    genFuncTerm :: [Int] -> Int -> FunctionTerm String String
    genFuncTerm [] c = Cell $ cells !! (c `mod` length cells)
    genFuncTerm [c] _ = Cell $ cells !! (c `mod` length cells)
    genFuncTerm [c, _] _ = Cell $ cells !! (c `mod` length cells)
    genFuncTerm [c, _, _] _ = Cell $ cells !! (c `mod` length cells)
    genFuncTerm (x:xr) c =
      let arity = x `mod` 2 + 1
          id = (x `div` 2) `mod` 3
          name = "f" ++ show id ++ "a" ++ show arity
          subStr = distribute arity xr
          subTerms = map (`genFuncTerm` c) subStr
       in Func name subTerms
    --
    distribute :: Int -> [Int] -> [[Int]]
    distribute n [] = replicate n []
    distribute n (x:xr) =
      if n <= 0
        then []
        else let sub = distribute n xr
              in tail sub ++ [x : head sub]

------------------------------------------------------------------------------
-- | 'genRandPredicateTerm' generates a random predicate term with arity 
-- up to 2
--
genRandPredicateTerm :: [String] -> IO String
genRandPredicateTerm cells = do
  n <- randomIO
  m <- randomIO
  let k = (n `mod` 2) + 1
  let p = (m `mod` 2) :: Int
  let ptstr = "q" ++ show p ++ "a" ++ show k
  funcTerms <- replicateM k (genRandFuncTerm cells)
  return $ filter (/= '\"') $ predTermToString $ Pred ptstr funcTerms

------------------------------------------------------------------------------
-- 'genRandUpdate' generates a random update
--
genRandUpdate :: [String] -> IO String
genRandUpdate cells = do
  n <- randomIO
  let k = n `mod` length cells
  ft <- genRandFuncTerm cells
  let cl = cells !! k
  return $ "[" ++ cl ++ " <- " ++ filter (/= '\"') (funcTermToString ft) ++ "]"

------------------------------------------------------------------------------
-- | 'genRandTSLForm' generates a random formula
--
genRandTSLForm :: Int -> IO String
genRandTSLForm size = do
  cells <- genRandCells
  m <- randomIO
  n <- randomIO
  upds <- replicateM (m `mod` 3 + 1) (genRandUpdate cells)
  pred <- replicateM (n `mod` 3 + 1) (genRandPredicateTerm cells)
  let k = length upds + length pred
  seed <- randomIO
  (ltl, aps) <- genRandLTL size (seed `mod` 10000000) k
  return $
    fst $
    foldl
      (\(form, index) elem ->
         (findAndReplace (aps !! index) elem form, index + 1))
      (ltl, 0)
      (upds ++ pred)

------------------------------------------------------------------------------
-- | 'genRandTSL' generates a TSL file with a random formula given path 
-- name and index
--
genRandTSL :: Int -> FilePath -> String -> Int -> IO ()
genRandTSL size path name index = do
  let file = path ++ name ++ show index ++ ".tsl"
  form <- genRandTSLForm size
  writeFile file $ "initially guarantee { " ++ form ++ "; }"

------------------------------------------------------------------------------
-- | 'fuzz' generates a given number of random TSL formulas and puts them
-- in some given directory 
--
fuzz :: Int -> Int -> FilePath -> IO ()
fuzz size n pth = do
  let path =
        if last pth == '/'
          then pth
          else pth ++ "/"
  mapM_ (genRandTSL size path ("randD" ++ show size ++ "_")) [1 .. n]

------------------------------------------------------------------------------
main :: IO ()
main = do
  args <- getArgs
  case args of
    [depthStr, numStr, basepath] ->
      case readMaybe depthStr of
        Nothing -> putStrLn $ "Error: " ++ depthStr ++ " is not a number"
        Just depth ->
          case readMaybe numStr of
            Nothing -> putStrLn $ "Error: " ++ numStr ++ " is not a number"
            Just num -> do
              exists <- doesDirectoryExist basepath
              if exists
                then fuzz depth num basepath
                else putStrLn $
                     "Error: " ++ basepath ++ " is not existing a directory"
    _ ->
      putStrLn $
      unlines
        [ "USAGE: tslfuzz <SIZE> <NUMBER> <BASEDIR>"
        , "  <SIZE>:    tree size given to randltl"
        , "  <NUMBER>:  number of formulas to generate"
        , "  <BASEDIR>: directory where the files should be generated"
        ]
------------------------------------------------------------------------------
