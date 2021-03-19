-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Maintainer  :  Philippe Heim
--
-- This tool applies the main satisfiability algorithm
--
-----------------------------------------------------------------------------
module Main where

-----------------------------------------------------------------------------
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import TSL (fromTSL)
import TSLSat (Result(..), sat, spotLTL2NBA, toBSA)

-----------------------------------------------------------------------------
helpText :: String
helpText =
  unlines
    [ "USAGE: tslsat [<OPTIONS>] <TSL-FILE>"
    , "  Remark: The TSL formula is interpreted as finitary TSL"
    , "  Options:"
    , "    --verbose: show intermediate steps"
    ]

-----------------------------------------------------------------------------
checkSat :: Bool -> FilePath -> IO ()
checkSat verbose filepath = do
  exists <- doesFileExist filepath
  if not exists
    then putStrLn "Error: file does not exists"
    else do
      content <- readFile filepath
      tsl <- fromTSL (Just filepath) content
      case tsl of
        Left error -> putStrLn $ "Error: " ++ show error
        Right spec -> do
          potBSA <- toBSA spotLTL2NBA spec
          case potBSA of
            Left error -> putStrLn $ "Error: " ++ show error
            Right bsa -> do
              result <- sat bsa verbose
              putStrLn $
                case result of
                  SAT -> "SAT"
                  UNSAT -> "UNSAT"
                  UNSAT_LTL -> "LTL-UNSAT"

-----------------------------------------------------------------------------
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--verbose", filename] -> checkSat True filename
    [filename] -> checkSat False filename
    _ -> putStrLn helpText
-----------------------------------------------------------------------------
