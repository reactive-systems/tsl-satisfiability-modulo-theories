-----------------------------------------------------------------------------
-- |
-- Module      :  TSLSat
-- Maintainer  :  Philippe Heim
--
-- This module is the interfacing module for the TSLSat library
--
-----------------------------------------------------------------------------
module TSLSat
  ( sat
  , Result(..)
  , BSA
  , bsaToString
  , toBSA
  , spotLTL2NBA
  , FunctionTerm(..)
  , PredicateTerm(..)
  , funcTermToString
  , predTermToString
  ) where

import Algorithm (Result(..), sat)
import BuechiStreamAutomaton (BSA, bsaToString)
import TSLToBSA (spotLTL2NBA, toBSA)
import Terms
  ( FunctionTerm(..)
  , PredicateTerm(..)
  , funcTermToString
  , predTermToString
  )
-----------------------------------------------------------------------------
