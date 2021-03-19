-----------------------------------------------------------------------------
-- |
-- Module      :  ExternalCall
-- Maintainer  :  Philippe Heim
--
-- This module provides a wrapper of calls to external programs used
-- throughout this project
--
-----------------------------------------------------------------------------
module ExternalCall
  ( runCMD
  ) where

-----------------------------------------------------------------------------
import System.Exit (ExitCode)
import System.IO
import System.Process (runInteractiveCommand, waitForProcess)

-----------------------------------------------------------------------------
-- | 'runCMD' takes an command and STDIN input, executes the command and
-- returns STDOUT, STDERR and the exit code
--
runCMD :: String -> String -> IO (String, String, ExitCode)
runCMD cmd stdin = do
  (i, o, e, p) <- runInteractiveCommand cmd
  hSetBuffering o NoBuffering
  hSetBuffering e NoBuffering
  hPutStr i stdin
  hClose i
  sout <- hGetContents o
  serr <- hGetContents e
  ecode <- length sout `seq` waitForProcess p
  return (sout, serr, ecode)
-----------------------------------------------------------------------------
