{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RankNTypes
           , LambdaCase #-}

module LCO.Core.Interpreter
    ( lLine
    , ilNum
    , lSort
    , lToken
    , lIdx
    , lKey
    , lAtop
    , lCompose
    , lBM
    , lBN
    , iN
    , ssOf
    , lAnB
    , lHead
    , lFind
    , lCopy
    , nFast
    , atomize
    , atomic1
    , atomic2
    , sym
    , tag
    , lFork
    , lHook
    , listsFrom
    , spOf
    , verb1
    , verb2
    , recD
    , runCon
    , lTie
    , rA
    , run
    , ast
    , vDict
    , aDict
    , cDict
    ) where

import LCO.Core.Types

import Control.Arrow
import Control.Monad
import Control.Lens hiding (noneOf, (.:))

import Data.Char
import Data.List
import Data.Maybe
import Data.Function
import Data.Semigroup
import Data.Composition
--import Data.Functor.Foldable
--import Data.Generics.Genifunctors
import Data.Monoid hiding ((<>))
import Data.Vector (Vector(..), (!))

import qualified Data.Set        as S
import qualified Data.Vector     as V
import qualified Data.Map.Strict as Map

import Text.ParserCombinators.Parsec

lLine :: Parser [String]
lLine = fmap (over traverse unwords . groupBy (flip (.) ilNum . (&&) . ilNum)) $ spaces >> many lToken


ilNum :: String -> Bool
ilNum s@(c:_) = (isDigit c || c == '_') && last s `notElem` ":."


lSort :: forall t a. Ord t => Shape a -> Shape t -> Shape a
lSort a b = let ((_, p), (_, q)) = listsFrom a b
    in (Shape (_shapeRank a) . V.concat) $ snd <$> sortOn fst (zip q p)


--lToken :: ParsecT String u Id String
lToken = (string "NB." >>= (<$> many anyChar) . (++))
     <|> do char '\''
            s <- concat <$> many (many1 (noneOf "'") <|> try (string "''"))
            char '\'' <?> "closing quote"
            return $ concat ["'", s, "'"]
     <|> ((++) <$> (many1 (char '_' <|> alphaNum) <|> count 1 anyChar)
               <*> many (oneOf ".:")
               >>= (spaces >>) . return)


lIdx :: Shape LNum -> Shape LNum
lIdx as = Shape [V.length v] v
    where v = V.concat [V.replicate (lNum2i $ (as^.shapeVec)!i) (i2LNum i)
            | i <- [0..V.length (as^.shapeVec) - 1]]


lKey :: forall a b. Semigroup b => Ord b => (LSingleton, a) -> Shape b -> Shape LNum -> Shape LNum
lKey v a b = let ((_, p), (_:ss, q)) = listsFrom a b
             in post [length $ nFast p]
             $ map (\ks -> (verb1 v . Shape (length ks:ss) . V.concat . map (q!!)) ks)
             $ (`elemIndices` p) <$> nFast p


lAtop :: (LSingleton, t) -> (LSingleton, LPair) -> (LSingleton, LPair)
lAtop u v@(LSingleton mv _, _) = (LSingleton mv $ verb1 u . verb1 v, LPair mv mv $ (verb1 u .) . verb2 v)


lCompose :: (LSingleton, LPair) -> (LSingleton, t) -> (LSingleton, LPair)
lCompose u v@(LSingleton mv _, _) = (LSingleton mv $ verb1 u . verb1 v, LPair mv mv (verb2 u `on` verb1 v))


lBM :: Shape LNum -> (t, LPair) -> (LSingleton, LPair)
lBM m v = (LSingleton maxBound $ verb2 v m, LPair 0 maxBound undefined)


lBN :: (t, LPair) -> Shape LNum -> (LSingleton, LPair)
lBN u n = (LSingleton maxBound $ flip (verb2 u) n, LPair 0 maxBound undefined)


iN :: String -> Bool
iN = all isAlpha


ssOf :: LNum -> Shape LNum
ssOf l = let Shape _ as = lOpen l in lOpen $ as!1


lAnB :: Noun -> Noun -> Noun
lAnB a b = Shape [V.length v] v
    where v = V.fromList $ i2LNum <$> f [] ms (lNum2i $ (b^.shapeVec)!0)
          ms = reverse $ lNum2i <$> (V.toList . _shapeVec) a

          f a [] _ = a
          f a (m:ms) n = let (q, r) = divMod n m
            in f (r:a) ms q


lHead :: forall a. Semigroup a => Shape a -> Shape a
lHead as | null rrs || r == 0 = as
         | otherwise = (Shape rs .:. V.slice) 0 (product rs) (as^.shapeVec)
         where rrs = as^.shapeRank
               (r:rs) = rrs


lFind :: String -> Token
lFind as = let ws = words as
    in case length ws of
         1 | all isDigit as         -> (TSingle . show) (read as :: Int)
           | Map.member as dict     -> dict Map.! as
           | otherwise              -> TEmpty
         _ | all (all isDigit) ws   -> (TSingle . show) (read <$> ws :: [Int])
           | otherwise              -> TEmpty
    where dict = Map.fromList [ ("#",  TDouble ("length", "replicate"))
                              , ("+",  TDouble ("memes", "(+)"))
                              , ("-",  TDouble ("negate", "(-)"))
                              , ("*",  TDouble ("signum", "(*)"))
                              , ("%",  TDouble ("(1/) . fromIntegral",
                                             "(\\x y -> fromIntegral x / fromIntegral y)"))
                              , (">:", TDouble ("(1+)", "(fromEnum .) . (>)"))
                              , ("i.", TDouble ("flip take [0..]",
                                             "(\\x y -> case elemIndex y x of " ++
                                             "{Just i -> i; n -> length x)}"))
                              , ("/",  TPair (("foldr1", 2), ("flip . (map .) . flip . (map .)", 2)))
                              , ("\\", TPair (("(. tail. inits) . map", 1), ("memes", 2)))
                              , ("(",  TLParen)
                              , (")",  TRParen)
                              ]


lCopy :: forall a. Semigroup a => Shape LNum -> Shape a -> Shape a
lCopy a b
    | null rrs && null sss = lCopy (Shape [1] av) (Shape [1] bv)
    | null rrs = let k = lNum2i (av!0) in (Shape (s*k:ss) . V.concat . replicate k) bv
    | null sss = let k = V.sum $ lNum2i <$> av in (Shape [k] . V.replicate k) (bv!0)
    | r /= s = error "length error"
    | otherwise = let k = (V.sum .: fmap) lNum2i av
                      sz = product ss
      in Shape (k:ss) $ V.concat [V.concat $ replicate (lNum2i $ av!i) $ V.slice (i*sz) sz bv | i <- [0..s-1]]
    where
        rrs = a^.shapeRank
        sss = b^.shapeRank
        av  = a^.shapeVec
        bv  = b^.shapeVec
        (s:ss) = sss
        (r:rs) = rrs


nFast :: forall a. Semigroup a => Ord a => [a] -> [a]
nFast = reverse . flip (f []) S.empty
    where f acc [] _ = acc
          f acc (a:as) seen
            | S.member a seen = f acc as seen
            | otherwise = f (a:acc) as (S.insert a seen)


atomize :: String -> LNum
atomize s
    | null s = lPuts ""
    | (length . words) s > 1 = maybe (lPuts "|syntax error") (tag 0 . fromList) . mapM readLNum . words $ s
    | Just l <- readLNum s = tag 0 $ singleton l
    | otherwise = lPuts s


atomic1 :: (LNum -> LNum) -> LSingleton
atomic1 f = let g as = singleton . f $ (V.head .: view) shapeVec as in LSingleton 0 g


atomic2 :: (LNum -> LNum -> LNum) -> LPair
atomic2 f = let g = singleton .: f `on` V.head . view shapeVec in LPair 0 0 g


sym :: forall a. Semigroup a => Map.Map String a -> LNum -> Maybe a
sym dict l | Just s <- lGetS l, iN s = Map.lookup s dict
           | otherwise = Nothing


tag :: forall a. Integral a => a -> Noun -> LNum
tag t a = B . fromList . over traverse B $ [(singleton . i2LNum) t, a]


lFork :: (LSingleton, LPair) -> (a, LPair) -> (LSingleton, LPair) -> (LSingleton, LPair)
lFork u v w = ( LSingleton maxBound $ verb2 v <$> verb1 u <*> verb1 w
              , LPair maxBound maxBound $ \a b -> verb2 v (verb2 u a b) (verb2 w a b)
              )


lHook :: forall a b. (a, LPair) -> (LSingleton, b) -> (LSingleton, LPair)
lHook u v = ( LSingleton maxBound $ \b -> verb2 u b $ verb1 v b
            , LPair maxBound maxBound $ \a b -> verb2 u a $ verb1 v b
            )


listsFrom :: forall a b. Shape a -> Shape b
          -> ( ([Int], [Vector a])
             , ([Int], [Vector b]) )
listsFrom (Shape rrs xs) (Shape sss ys)
    | r /= s = error "length error"
    | otherwise = ((r:rs, p), (s:ss, q))
    where (r:rs) = if null rrs then 1:rrs else rrs
          (s:ss) = if null sss then 1:sss else sss
          p = [V.slice (i*sz) sz xs | i <- [0..r-1]]
          q = [V.slice (i*sz) sz ys | i <- [0..s-1]]
          sz = product ss


spOf :: Map.Map String LNum -> LNum -> Maybe (LSingleton, LPair)
spOf dict l
    | Just s <- lGetS l, s == "$:" = Just . ap recD (Map.! "$:") $ dict
    | Just s <- lGetS l, Just v <- Map.lookup s vDict = Just v
    | Just s <- (lGetS . V.head) as, Just a <- Map.lookup s aDict =
        let Just v = spOf dict (args!0)
        in  Just $ a v
    | Just s <- (lGetS . V.head) as, s /= "`", Just c <- Map.lookup s cDict =
        Just $ if s == "@."
               then rA dict (args!0) (args!1) else runCon dict c (args!0) (args!1)
    | Just i <- (lGetI . V.head) as, i == 2 =
        let [Just u, Just v] = spOf dict <$> V.toList args
        in Just $ lHook u v
    | Just i <- (lGetI . V.head) as, i == 3 =
        let [Just u, Just v, Just w] = spOf dict <$> V.toList args
        in Just $ lFork u v w
    | otherwise = Nothing
    where Shape rs as  = lOpen l
          Shape _ args = lOpen $ as!1


verb1 :: forall a. (LSingleton, a) -> Shape LNum -> Shape LNum
verb1 (LSingleton mu u, _) = go1 (i2LNum 0) mu u


verb2 :: forall a. (a, LPair) -> Shape LNum -> Shape LNum -> Shape LNum
verb2 (_, LPair lu ru u) = go2 (i2LNum 0) lu ru u


recD :: Map.Map String LNum -> LNum -> (LSingleton, LPair)
recD dict l =
    let v = (fromJust . spOf dict) l
    in (LSingleton maxBound $ verb1 v, LPair maxBound maxBound $ verb2 v)


runCon dict (nn, nv, vn, vv) l0 l1
    | [Nothing, Nothing] <- spOf dict <$> [l0, l1] = nn m n
    | [Nothing,  Just v] <- spOf dict <$> [l0, l1] = nv m v
    | [Just u,  Nothing] <- spOf dict <$> [l0, l1] = vn u n
    | [Just u,   Just v] <- spOf dict <$> [l0, l1] = vv u v
    where m = (ssOf .: run) dict l0
          n = (ssOf .: run) dict l1


lTie :: Map.Map String LNum -> LNum -> LNum -> LNum
lTie d l0 l1
    | [Nothing, Nothing] <- spOf d <$> [l0, l1] = undefined
    | [Nothing,  Just _] <- spOf d <$> [l0, l1] = tag 0 $ Shape [r+1] $ V.snoc xs l1
    | [Just _ , Nothing] <- spOf d <$> [l0, l1] = tag 0 $ Shape [s+1] $ V.cons l0 ys
    | [Just _ ,  Just _] <- spOf d <$> [l0, l1] = tag 0 $ fromList [l0, l1]
    where Shape [r] xs = (ssOf .: run) d l0
          Shape [s] ys = (ssOf .: run) d l1


rA :: Map.Map String LNum -> LNum -> LNum -> (LSingleton, LPair)
rA d l0 l1
    | [Nothing, Nothing] <- spOf d <$> [l0, l1] = ag  d m n
    | [Nothing,  Just v] <- spOf d <$> [l0, l1] = agM d m v
    | [Just u , Nothing] <- spOf d <$> [l0, l1] = undefined
    | [Just u ,  Just v] <- spOf d <$> [l0, l1] = undefined
    where m = run d l0 & ssOf
          n = run d l1 & ssOf

          ag d (Shape rs as) (Shape ss bs)
              | length rs > 1 || length ss > 1 = error "rank error"
              | null rs = ag d (Shape [1] as) (Shape ss bs)
              | null ss = as ! (lNum2i . V.head) bs & fromJust . spOf d

          agM d m@(Shape rs as) v@(LSingleton mv _, LPair lv rv _) =
              ( LSingleton mv $ \n -> verb1 (ag d m $ verb1 v n) n
              , LPair lv rv $ \m n -> verb2 (ag d m $ verb2 v m n) m n
              )


run :: Dict -> LNum -> LNum
run dict l | Just a <- sym dict l = a
           | null rs = l
           | Just i <- (lGetI . V.head) as = case i of 0 -> l
           | Just "`" <- (lGetS . V.head) as = lTie dict (args!0) (args!1)
           | Just v <- spOf dict' $ as ! 0 = case V.length args of
                 1 -> let y = ssOf $ run dict' (args!0) in tag 0 $ verb1 v y
                 2 -> let
                    x = (ssOf .: run) dict' (args!0)
                    y = (ssOf .: run) dict' (args!1)
                    in tag 0 $ verb2 v x y
    where Shape rs as = lOpen l
          Just word = (lGetS . V.head) as
          Shape _ args = lOpen $ as!1
          dict' = Map.insertWith (flip const) "$:" (as!0) dict


ast :: Bool -> Dict -> [String] -> [LNum] -> (Maybe LNum, Dict)
ast echo dict as st
    | length st < 4 = shift
    | ecl, isV l1, isN l2 = reduce (l0:l1:run dict (B $ fromList [l2, B $ fromList [l1, l3]]):rest)
    | eclavn, isV l1, isV l2, isN l3 = reduce (l0:l1:run dict (B $ fromList [l2, B $ singleton l3]):rest)
    | eclavn, isN l1, isV l2, isN l3 = reduce (l0:run dict (B $ fromList [l2, B $ fromList [l1,l3]]):rest)
    | eclavn, isV l1, isA l2 = reduce (l0:B (fromList [l2, B $ singleton l1]):l3:rest)
    | eclavn, isV l1 || isN l1, isC l2, isV l3 || isN l3 = reduce (l0:B (fromList [l2, B $ fromList [l1, l3]]):rest)
    | eclavn, isV l1, isV l2, isV l3 = reduce (l0:B (fromList [B $ singleton $ i2LNum 3, B $ fromList [l1, l2, l3]]):l3:rest)
    | ecl, isV l1, isV l2 = reduce (l0:B (fromList [B $ singleton $ i2LNum 2, B $ fromList [l1, l2]]):l3:rest)
    | Just name <- lGetS l0, match l1 ["=.", "=:"], isCAVN l2 = ast False (Map.insert name l2 dict) as (l2:l3:rest)
    | match l0 ["("], isCAVN l1, match l2 [")"] = reduce (l1:l3:rest)
    | otherwise = shift
    where (l0:l1:l2:l3:rest) = st
          ecl = match l0 ["", "=.", "=:", "("]
          eclavn = ecl || isA l0 || isV l0 || isN l0
          f = sym dict

          isA l | Just x <- f l = isA x
                | Just s <- lGetS l = s `Map.member` aDict
                | Shape [2] as <- lOpen l, Just i <- (lGetI . V.head) as = i == 4
                | otherwise = False

          isV l | Just x <- f l = isV x
                | Just s <- lGetS l = s `Map.member` vDict
                | Shape [2] as <- lOpen l, Just i <- (lGetI . V.head) as = i == 2 || i == 3
                | Shape [2] as <- lOpen l = isA (as!0) || (isC (as!0) && Just "`" /= lGetS (as!0))
                | otherwise = False

          isN l | Just a <- f l = isN a
            | Shape [2] as <- lOpen l, Just i <- (lGetI . V.head) as = i == 0
                | Shape [2] as <- lOpen l = isV (as!0) || Just "`" == lGetS (as!0)
                | otherwise = False

          isC l | Just a <- f l = isC a
                | Just s <- lGetS l = s `Map.member` cDict
                | otherwise = False

          isCAVN l = isC l || isA l || isV l || isN l
          match l ss | Just s <- lGetS l = s `elem` ss
                     | otherwise = False
          encNoun a = B . fromList . over traverse B $ [(singleton . i2LNum) 0] ++ a

          shift | (h:t) <- as   = ast echo dict t $ atomize h:st
                | otherwise     = (out, dict)

          out | not echo        = Nothing
                | [_,_]   <- st = Nothing
                | [_,a,_] <- st = Just a
                | otherwise     = Just $ lPuts $ "|syntax error: " <> show st

          reduce = ast True dict as
          sym d l | Just s <- lGetS l, iN s = Map.lookup s d
                  | otherwise = Nothing


vDict :: Map.Map String (LSingleton, LPair)
vDict = Map.fromList
    [ ("+:", (atomic1 $ join lAdd, undefined))
    , ("+",  (undefined, atomic2 lAdd))
    , ("*:", (atomic1 $ join lMul, undefined ))
    , ("*",  (atomic1 $ i2LNum . signum . lNum2i, atomic2 lMul))
    , ("-:", (atomic1 $ flip lDiv (i2LNum 2), undefined))
    , ("-",  (atomic1 $ (lSub . i2LNum) 0, atomic2 lSub))
    , ("^.", (atomic1 lLog, undefined))
    , ("^",  (atomic1 lExp, atomic2 lPow))
    , ("%:", (atomic1 lSqrt, undefined))
    , ("%",  (atomic1 $ lDiv (i2LNum 1), atomic2 lDiv))
    , ("<",  (LSingleton maxBound $ \x -> singleton $ B x, atomic2 lLT))
    , ("<.", (atomic1 lFloor, atomic2 min))
    , (">",  (LSingleton 0 $ \ss -> (lOpen . V.head) (ss^.shapeVec), atomic2 lGT))
    , ("<:", (atomic1 $ lAdd (i2LNum (-1)), atomic2 lLE))
    , (">:", (atomic1 $ lAdd (i2LNum 1), atomic2 lGE))
    , ("=",  (undefined, atomic2 lEQ))
    , ("[",  (LSingleton maxBound id, LPair maxBound maxBound const))
    , ("]",  (LSingleton maxBound id, LPair maxBound maxBound $ flip const))
    , ("$:", (LSingleton maxBound $ (const . singleton . lPuts) "|stack error", LPair maxBound maxBound $ \_ _ -> (singleton . lPuts) "|stack error"))
    , ("|",  (atomic1 lMag, atomic2 lRes))
    , ("#:", (LSingleton maxBound undefined, LPair 1 0 lAnB))
    , ("I.", (LSingleton 1 lIdx, LPair maxBound maxBound undefined))
    , ("/:", (undefined, LPair maxBound maxBound lSort))
    , ("{.", (LSingleton maxBound lHead, undefined))
    , ("1:", (LSingleton maxBound $ const $ singleton $ i2LNum 1, LPair maxBound maxBound $ \_ _ -> (singleton . i2LNum) 1))
    , ("i.", (LSingleton 1 $ \ss -> let ns = lNum2i <$> V.toList (ss^.shapeVec) in shapeList ns $ i2LNum <$> [0..product ns - 1], undefined))
    , ("j.", (atomic1 $ lMul (Z (0,1)), atomic2 $ \a b -> lAdd a (lMul (Z (0,1)) b)))
    , (",:", (LSingleton maxBound $ \ss -> Shape (1:(ss^.shapeRank)) (ss^.shapeVec), LPair maxBound maxBound $ \a b -> post [2] [a, b]))
    , (",",  (LSingleton maxBound $ \ss -> Shape [product (ss^.shapeRank)] (ss^.shapeVec), undefined))
    , ("#",  (LSingleton maxBound $ \ss -> (singleton . i2LNum . head) (ss^.shapeRank), LPair 1 maxBound lCopy))
    , ("x:", (LSingleton 1 $ \ss -> Shape (ss^.shapeRank) $ lExt <$> (ss^.shapeVec), undefined))
    , ("$",  (LSingleton maxBound $ \ss -> Shape [length (ss^.shapeRank)] $ V.fromList $ i2LNum <$> (ss^.shapeRank), undefined))]


aDict :: Map.Map String ((LSingleton, LPair) -> (LSingleton, LPair))
aDict = Map.fromList
    [ ("/", \v@(_, LPair lu ru op) ->
            ( LSingleton maxBound $ \ss -> case (ss^.shapeRank) of
                [] -> ss
                (r:rest) -> foldl1' (verb2 v) [Shape rest $ V.slice (i*sz) sz (ss^.shapeVec)
                  | i <- [0..r-1], let sz = product rest], LPair lu maxBound $ go2 (i2LNum 0) lu ru op
      ))
    , ("\\", \v ->
        (LSingleton maxBound $ \ss -> case (ss^.shapeRank) of
            [] -> ss
            (r:rest) -> post [r] $ map (verb1 v) $ zipWith (\i as -> Shape (i:rest) as) [1..r] [V.slice 0 (i*sz) (ss^.shapeVec)
                | i <- [1..3], let sz = product rest], undefined
        ))
    , ("/.", \v -> (undefined, LPair maxBound maxBound $ lKey v))
    , ("~", \v@(_, LPair ru lu _) ->
        ( LSingleton maxBound $ \a   -> verb2 v a a
        , LPair  ru lu    $ \a b -> verb2 v b a
        ))
    ]


cDict = Map.fromList
    [ ("&",  ( undefined,       lBM,       lBN,  lCompose ))
    , ("@",  ( undefined, undefined, undefined,     lAtop ))
    , ("@.", ( undefined, undefined, undefined, undefined ))
    , ("`",  ( undefined, undefined, undefined, undefined ))
    ]
