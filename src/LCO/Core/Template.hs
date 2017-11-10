{-# LANGUAGE Trustworthy       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE FlexibleInstances #-}

-------------------------------------------------------------------------------
-- |
-- Module      : LCO.Core.Template
-- Description : Templates for a proper codegen and debug
-- Copyright   : (c) Adam, 2017
-- License     : MIT
-- Maintainer  : awkure@protonmail.ch
-- Stability   : experimental
-- Portability : POSIX
-------------------------------------------------------------------------------

module LCO.Core.Template
    ( mkShowFields
    , curryN
    , genCurry
    ) where

import Control.Monad
import Control.Arrow
import Control.Lens

import Data.Composition

import Language.Haskell.TH

mkShowFields :: Name -> Q [Dec]
mkShowFields name = do
    TyConI (DataD _ _ _ _ [RecC _ fld] _) <- reify name -- lens here

    let names = over traverse (\(name,_,_) -> name) fld -- lens here

        showField :: Name -> Q Exp
        showField name = [|\a -> s ++ " = " ++ show ($(varE name) a)|]
            where s = nameBase name

        showFields :: Q Exp
        showFields = (listE .: map) showField names

    [d|instance Show $(conT name) where
            show a = intercalate ", " (map ($ a) $showFields)|]


curryN :: Int -> Q Exp
curryN n = do
    f  <- newName "f"
    xs <- replicateM n (newName "x")

    let args = over traverse VarP (f:xs)
        ntup = TupE . over traverse VarE $ xs

    (return . LamE args .: AppE) (VarE f) ntup


genCurry :: Int -> Q [Dec]
genCurry n = forM [1..n] mkCurry
    where mkCurry i = funD name [clause [] (normalB (curryN i)) []]
            where name = mkName $ "curry" ++ show i
