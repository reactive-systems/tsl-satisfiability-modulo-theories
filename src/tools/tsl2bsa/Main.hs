-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Maintainer  :  Philippe Heim
--
-- This tool can be used to print a BSA
--
-----------------------------------------------------------------------------
module Main where

-----------------------------------------------------------------------------
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import TSL (fromTSL)
import TSLSat (bsaToString, spotLTL2NBA, toBSA)

-----------------------------------------------------------------------------
main :: IO ()
main = do
  args <- getArgs
  case args of
    [filepath] -> do
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
                Right bsa -> putStrLn (bsaToString bsa)
    _ -> putStrLn "Usage: tsl2hoa <TSL-FILE>"
-----------------------------------------------------------------------------
