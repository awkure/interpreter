{-# LANGUAGE Safe #-}
{-# LANGUAGE CPP  #-}
-------------------------------------------------------------------------------
-- |
-- Module      : LCO.Core
-- Description : Imports all modules
-- Copyright   : (c) Adam, 2017
-- License     : MIT
-- Maintainer  : awkure@protonmail.ch
-- Stability   : stable
-- Portability : POSIX
-------------------------------------------------------------------------------

module LCO.Core
    ( module LCO.Core.Template
    , module LCO.Core.Types
    , module LCO.Core.Interpreter
    ) where

import LCO.Core.Template
import LCO.Core.Types
import LCO.Core.Interpreter

#ifdef HLINT
{-# ANN module "Hlint: ignore Use import/export shortcut" #-}
#endif
