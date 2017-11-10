module Main where


import LCO.Core

import qualified Data.Map.Strict as MS

import Data.List        (isPrefixOf)
import Data.Maybe       (fromJust, isNothing)
import Data.Semigroup   ((<>))
import Data.Vector      ((!))
import Control.Monad    (unless)
import System.IO        (stdin, stdout, hFlush, isEOF)

import Text.ParserCombinators.Parsec

main :: IO ()
main = repl MS.empty


repl :: Dict -> IO ()
repl d = do
    putStr "   | "
    hFlush stdout
    done <- isEOF
    unless done $ do
        s <- getLine
        let (out, d') = eval d s
        (unless (isNothing out) . putStrLn . fromJust) out
        repl d'


eval :: Dict -> String -> (Maybe String, Dict)
eval d s =
    case parse lLine "" s of
      Left  e -> (Just $ "| " <> show e, d)
      Right w -> let
        xs = "" : reverse ("" : filter (not . isPrefixOf "NB.") w)
        (ml, d') = ast True d xs []
        in (dump <$> ml, d')


dump :: LNum -> String
dump l = let Shape _ xs = lOpen l in
    case lGetI $ xs!0 of
      Just 0  -> show . lOpen $ xs!1
      Nothing -> show l
