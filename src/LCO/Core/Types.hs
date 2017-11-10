{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TemplateHaskell
           , TemplateHaskellQuotes
           , DeriveFoldable
           , DeriveTraversable
           , DeriveFunctor
           , RankNTypes
           , FlexibleContexts
           , KindSignatures #-}

-------------------------------------------------------------------------------
-- |
-- Module      : LCO.Core.Types
-- Description : All helper functions, types and binings lies here
-- Copyright   : (c) Adam, 2017
-- License     : MIT
-- Maintainer  : awkure@protonmail.ch
-- Stability   : stable
-- Portability : POSIX
-------------------------------------------------------------------------------

module LCO.Core.Types (module LCO.Core.Types) where

import LCO.Core.Template

import Control.Arrow
import Control.Monad
import Control.Lens hiding ((.:))
import Data.Ratio
import Data.Char
import Data.Ord
import Data.List
import Data.Vector (Vector, (!))
import Data.Semigroup
import Data.Function
import Data.Composition
import Text.Printf

import qualified Data.Map.Strict as MS
import qualified Data.Vector as V

-- TODO : transformers
data Shape a = Shape { _shapeRank :: {-# UNPACK #-}![Int]
                     , _shapeVec  :: {-# UNPACK #-}!(Vector a)
                     } deriving (Eq, Functor, Foldable, Traversable)

makeLenses ''Shape
makePrisms ''Shape

data Token = TSingle String
           | TDouble {-# UNPACK #-}!(String, String)
           | TPair {-# UNPACK #-}!((String, Int), (String, Int))
           | TConj
           | TCop
           | TLParen
           | TRParen
           | TEmpty
           deriving (Show, Eq)

makeLenses ''Token
makePrisms ''Token

newtype Fix (f :: * -> *) = Int { _unfix :: f (Fix f) }

type Algebra   f a = f a -> a
type RAlgebra  f a = a -> f a
type CAlgebra  f a = (Fix f, a) -> a
type CVAlgebra f a = a -> Either (Fix f) a


type Dict       = MS.Map String LNum
type Noun       = Shape LNum
data LSingleton = LSingleton { mn :: Int, mr :: (Noun -> Noun) }
data LPair      = LPair { dn1 :: Int, dn2 ::  Int, dr :: (Noun -> Noun -> Noun) }


data LNum = I Integer
          | X Integer
          | Q (Ratio Integer)
          | D Double
          | Z (Double, Double)
          | B (Shape LNum)
          | S String
          deriving Eq


instance Semigroup LNum where
    (<>) = lAdd


instance Show LNum where
    show (S a) = show a
    show (I a) = lsi a
    show (X a) = lsi a
    show (Q a) = lsi (numerator a) <> (if denominator a == 1 then "" else 'r' : show (denominator a))
    show (D a) = lsd a
    show (Z (r, i)) = lsd r <> (if i == 0 then "" else 'j' : lsd i)
    show (B b) = "[" <> show b <> "]"


instance Ord LNum where
    compare (I a) (I b) = compare a b
    compare (X a) (X b) = compare a b
    compare (Q a) (Q b) = compare a b
    compare (D a) (D b) = compare a b
    compare (Z a) (Z b) = error "domain error"
    compare a b = uncurry compare $ cast a b


instance (Semigroup a, Show a) => Show (Shape a) where
    show (Shape sh xs) = showShape xs sh 0


lsi :: forall a. Ord a => Num a => Show a => a -> String
lsi n | n < 0     = '_' : lsi (-n)
      | otherwise = show n


lsd :: forall a. Ord a => Num a => PrintfArg a => a -> String
lsd n | n < 0 = '_' : lsd (-n)
      | '.' `elem` s = (reverse . dropWhile (`elem` "0.") . reverse) s
      | otherwise = s
      where s = printf "%.6g" n


showShape :: forall a. Semigroup a => Show a => Vector a -> [Int] -> Int -> String
showShape xs rs k =
    case rs of
      [ ]    -> show    $ xs ! k
      [n]    -> unwords $ showShape xs [] <$> (k +) <$>  [0..n-1]
      (n:ns) -> unlines $ showShape xs ns <$> (k +) <$> ([0..n-1] <&> (product ns *))


singleton :: a -> Shape a
singleton = Shape ([]) <<< V.singleton


fromList :: [a] -> Shape a
fromList = Shape . return . length <*> V.fromList


shapeList :: [Int] -> [a] -> Shape a
shapeList shape = Shape shape <<< V.fromList . (product >>> take) shape . cycle


fill :: a -> [Int] -> Shape a -> Vector a
fill z newRank ss
    | newRank == ss^.shapeRank = ss^.shapeVec
    | otherwise = V.replicate (product newRank) z V.//
        zip (sum . zipWith (*) (scanl1 (*) (1:reverse newRank)) . reverse <$> sequence (flip take [0..] <$> ss^.shapeRank))
            ((V.toList . view shapeVec) ss)


homogenize :: forall a. a -> [Int] -> [Shape a] -> Shape a
homogenize z frame xs = Shape (frame ++ resRank) $ V.concat $ fill z resRank <$> xs
    where origs   = xs^..traverse.shapeRank
          m       = maximum $ length <$> origs
          exts    = flip (over traverse) origs $ \xs -> replicate (m - length xs) 1 ++ xs
          resRank = foldl1' (zipWith max) exts


go1 :: a -> Int -> (Shape a -> Shape a) -> Shape a -> Shape a
go1 z mv v (Shape shape xs) = homogenize z fr
    [v (Shape rank $ V.slice (i*sz) sz xs) | i <- [0..product fr-1]]
    where (fr, rank) = flip splitAt shape $ ls - min mv ls
          ls = length shape
          sz = product rank


go2 :: a -> Int -> Int -> (Shape a -> Shape a -> Shape a) -> Shape a -> Shape a -> Shape a
go2 z lv rv v (Shape rs xs) (Shape ss ys)
    | or $ zipWith (/=) fX fY = error "frame mismatch"
    | length fX > length fY = f (flip v) (fY, rY) ys (fX, rX) xs
    | otherwise = f v (fX, rX) xs (fY, rY) ys
    where dimL = length rs - min lv (length rs)
          dimR = length ss - min rv (length ss)
          (fX, rX) = splitAt dimL rs
          (fY, rY) = splitAt dimR ss

          f v (fX, rX) xs (fY, rY) ys = homogenize z fY $
              concat [[v (Shape rX $ V.slice (i*xsz) xsz xs) (Shape rY $ V.slice ((i*m + j)*ysz) ysz ys)
                | j <- [0..m-1] ]
                | i <- [0..product fX-1]]
              where xsz = product rX
                    ysz = product rY
                    m = div (V.length ys * xsz) (V.length xs * ysz)


ts1 :: (a -> a) -> Shape a -> Shape a
ts1 f = singleton . f . (! 0) . _shapeVec

ts2 :: (a -> a -> a) -> Shape a -> Shape a -> Shape a
ts2 f = singleton .: f `on` (! 0) <<< _shapeVec


-- TODO : TH
lGetS :: LNum -> Maybe String
lGetS (B (Shape [] ss)) | S s <- ss V.! 0 = Just s
                        | otherwise = Nothing
lGetS _ = Nothing


lGetI :: LNum -> Maybe Integer
lGetI (B (Shape [] xs)) | I x <- xs V.! 0 = Just x
                        | otherwise = Nothing
lGetI _ = Nothing


lOpen :: LNum -> Shape LNum
lOpen (B a) = a
lOpen a = singleton a


lPuts :: String -> LNum
lPuts = B . singleton . S


post :: [Int] -> [Shape LNum] -> Shape LNum
post fr xs = tM $ homogenize (i2LNum 0) fr xs
    where tM :: Shape LNum -> Shape LNum
          tM a@(Shape rs xs)
              | V.null xs = a
              | otherwise = let
                b :: LNum
                b = V.foldl1' ((fst .) <<< cast) xs
                in Shape rs $ fst . (`cast` b) <$> xs


checkOverflow :: Integer -> LNum
checkOverflow z
  | z >= -2^63 && z <= 2^63 - 1= I z
  | otherwise = D . fromIntegral $ z


readLNum :: String -> Maybe LNum
readLNum s
    | all isDigit s = Just $ checkOverflow (read s :: Integer)
    | head s == '\''= (Just . S . init . tail) s
    | otherwise     = Nothing


i2LNum :: Integral a => a -> LNum
i2LNum = checkOverflow . fromIntegral


lNum2i :: LNum -> Int
lNum2i (I a) = fromIntegral a
lNum2i (X a) = fromIntegral a
lNum2i _ = error "domain error"


-- TODO : TH
cast :: LNum -> LNum -> (LNum, LNum)
cast (I a) (I b) = (I a, I b)
cast (X a) (X b) = (X a, X b)
cast (Q a) (Q b) = (Q a, Q b)
cast (D a) (D b) = (D a, D b)
cast (Z a) (Z b) = (Z a, Z b)
cast (I a) (X b) = (X a, X b)
cast (I a) (Q b) = (Q $ a % 1, Q b)
cast (I a) (D b) = (D $ fromIntegral a, D b)
cast (I a) (Z b) = (Z (fromIntegral a, 0), Z b)
cast (X a) (Q b) = (Q $ a % 1, Q b)
cast (X a) (D b) = (D $ fromIntegral a, D b)
cast (X a) (Z b) = (Z (fromIntegral a, 0), Z b)
cast (Q a) (D b) = (D $ fromRational a, D b)
cast (Q a) (Z b) = (Z (fromRational a, 0), Z b)
cast (D a) (Z b) = (Z (a, 0), Z b)
cast (B a) (B b) = (B a, B b)
cast _ (B b) = error "domain error"
cast x y = cast y x


lAdd (I x) (I y) = (checkOverflow .: (+)) x y
lAdd (X x) (X y) = X (x + y)
lAdd (Q x) (Q y) = Q (x + y)
lAdd (D x) (D y) = D (x + y)
lAdd (Z (a, b)) (Z (c, d)) = Z (a + c, b + d)
lAdd x y = (uncurry lAdd .: cast) x y

lMul (I x) (I y) = (checkOverflow .: (*)) x y
lMul (X x) (X y) = X (x * y)
lMul (Q x) (Q y) = Q (x * y)
lMul (D x) (D y) = D (x * y)
lMul (Z (a, b)) (Z (c, d)) = Z (a*c - b*d, a*d + b*c)
lMul x y = (uncurry lMul .: cast) x y

lSub (I x) (I y) = (checkOverflow .: (-)) x y
lSub (X x) (X y) = X (x - y)
lSub (Q x) (Q y) = Q (x - y)
lSub (D x) (D y) = D (x - y)
lSub (Z (a, b)) (Z (c, d)) = Z (a - c, b - d)
lSub x y = (uncurry lSub .: cast) x y

lDiv (I x) (I y) = (lDiv `on` D . fromIntegral) x y
lDiv (X x) (X y) = Q (x % y)
lDiv (Q x) (Q y) = Q (x / y)
lDiv (D x) (D y) = D (x / y)
lDiv (Z (a, b)) (Z (c, d)) = (Z .: (,) `on` (/ (((+) `on` (**2)) b d))) (a*c + b*d) (b*c - a*d)
lDiv x y = (uncurry lDiv .: cast) x y


li2trig (Z (a, b)) = Z (r, phi)
     where r = sqrt ((a^2) + (b^2))
           phi | a < 0 = (atan (b/a)) + pi
               | a < 0 && b < 0 = (atan (b/a)) - pi
               | otherwise = atan (b/a)

n2pi n (Z (a, b)) = (n ** a) * (cos (b * log n) + sin (b * log n))

lPow (I x) (I y) = (D .: (**) `on` fromIntegral) x y
lPow (X x) (X y) = X (x^y)
lPow (Q x) (Q y) = lPow (D $ fromRational x) (D $ fromRational y)
lPow (D x) (D y) = D (x**y)
{-
lPow x@(Z (a, b)) y@(Z (c, d)) = Z (r * sin (xphi *  , )
    where (Z (rx, xphi)) = li2trig x
          (Z (ry, yphi)) = li2trig y
          r = (rx ** c) * (n2pi rx d)
-}
lPow (Z (a, b)) (Z (c,d)) = undefined
lPow x y = (uncurry lPow .: cast) x y

lSqrt (I x) = D . sqrt . fromIntegral $ x
lSqrt (X x) = D . sqrt . fromIntegral $ x
lSqrt (Q x) = D . sqrt . fromRational $ x
lSqrt (D x) = D . sqrt $ x
lSqrt a@(Z x) = (Z .: (,) `on` (r *)) (cos tr) (sin tr)
    where (Z (r, phi)) = li2trig a
          tr = flip (/) 2 $ phi + 2 * pi

lExp (I x) = D . exp . fromIntegral $ x
lExp (X x) = D . exp . fromIntegral $ x
lExp (Q x) = D . exp . fromRational $ x
lExp (D x) = D . exp $ x
lExp (Z x) = undefined

lLog (I x) = D . log . fromIntegral $ x
lLog (X x) = D . log . fromIntegral $ x
lLog (Q x) = D . log . fromRational $ x
lLog (D x) = D . log $ x
lLog (Z x) = undefined

lRes (I x) (I y) = I $ mod y x
lRes (X x) (X y) = X $ mod y x
lRes (Q x) (Q y) = undefined
lRes (D x) (D y) = undefined
lRes (Z (a, b)) (Z (c, d)) = undefined
lRes x y = (uncurry lRes .: cast) x y

lExt (I x) = X x
lExt (X x) = X x
lExt (Q x) = Q x
lExt (D x) = (Q .: approxRational) x 1e-6
lExt (Z x) = error "domain error"

lMag (I x) = I . abs $ x
lMag (X x) = X . abs $ x
lMag (Q x) = Q . abs $ x
lMag (D x) = D . abs $ x
lMag (Z (a, b)) = (D . sqrt .: (+) `on` (^2)) a b

lFloor (I x) = I x
lFloor (X x) = X x
lFloor (Q x) = X . floor $ x
lFloor (D x) = I . floor $ x
lFloor (Z (x, y)) = (Z .: (,) `on` fromIntegral . floor) x y

lEQ, lLT, lLE, lGT, lGE :: forall a. Ord a => a -> a -> LNum
lLT = lB .: (<)
lLE = lB .: (<=)
lGT = lB .: (>)
lGE = lB .: (>=)
lEQ = lB .: (==)

lB = I . fromIntegral . fromEnum
