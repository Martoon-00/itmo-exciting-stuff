{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | ~3*n/4 solution of OneMax problem.

module Main where

import           Control.Monad         (forM, forM_, replicateM, void)
import           Data.List             (group, sort)
import           Prelude               hiding (interact)
import           System.IO             (hClose, hFlush, stdin, stdout)

import           Control.Monad.ST.Lazy as ST
import qualified Data.Array            as A
import qualified Data.Array.IO.Safe    as A
import qualified Data.Array.ST.Safe    as A
import qualified Data.Bits             as B

import           Debug.Trace

main :: IO ()
main = interact $ map (unwords . map show) . process . map read . words
  where
    process (n:fs) = solve n fs
    process _      = error "not enought input"

interact :: (String -> [String]) -> IO ()
interact f = do
    input <- getContents
    forM_ (f input) $ \line -> putStrLn line >> hFlush stdout
    mapM_ hClose [stdout, stdin]

type Seed = Int
type Fitness = Int
type Flips = [Int]
type InputOutput = [Fitness] -> [Flips]

random :: Seed -> (Seed, Int)
random s = (s * 99139) `divMod` 95279

randomListR :: Enum a => Seed -> (a, a) -> [a]
randomListR s (l, r) =
    let (s', g) = random s
        i = (g `mod` (fromEnum r - fromEnum l + 1)) + fromEnum l
    in  toEnum i : randomListR s' (l, r)

shuffle :: Seed -> [a] -> A.Array Int a
shuffle seed content = A.runSTArray $ do
    let n = length content
    array <- A.newListArray (1, n) content
    go n (seed * 237) array
    return array
  where
    go 1 _ _ = return ()
    go k s a = do
        let (s', g) = (s * 99139) `divMod` 95279
            i = (g `mod` k) + 1
        x <- A.readArray a k
        y <- A.readArray a i
        A.writeArray a i x
        A.writeArray a k y
        go (k - 1) s' a

genPermutation :: Seed -> Int -> A.Array Int Int
genPermutation seed n = shuffle seed [1..n]

confuse :: Int -> Int -> Flips -> Flips
confuse seed n =
    let permutation = genPermutation seed n
    in  map $ \x -> permutation A.! x

addToNext :: Flips -> [Flips] -> [Flips]
addToNext f' (f:fs) = (f' ++ f) : fs
addToNext f' []     = [f']

-- | Helper for safe requests
request :: Flips -> (Fitness -> InputOutput) -> InputOutput
request req f inpss = cleanFlips req : let (!inp:inps) = inpss in f inp inps

atLeastOneFlip :: [Flips] -> [Flips]
atLeastOneFlip [] = [[1], [1]]
atLeastOneFlip fs = fs

noMoreThan :: Int -> [a] -> [a]
noMoreThan _ []     = []
noMoreThan 0 _      = error "Too many values"
noMoreThan k (x:xs) = x : noMoreThan (k - 1) xs

expect :: Fitness -> Fitness -> InputOutput
expect x y
    | x == y = const []
    | otherwise = error "Didn't reach end unexpectedly"

limit :: Int -> Int
limit n = (+ 50) . round $ (fromIntegral n / 4 * 3 :: Double)

cleanFlips :: Flips -> Flips
cleanFlips = map head . filter (odd . length) . group . sort

chunkSize :: Int
chunkSize = 10

solve :: Int -> InputOutput
solve n inps =
    let (fi:fs) = inps
    in noMoreThan (limit n) . atLeastOneFlip . map cleanFlips $ process fi 1 fs
  where
    process !f i
        | i > n = expect f n
        | otherwise =
        let len = min chunkSize (n - i + 1)
            initVariants = buildVariantsCached len
            indices = [i .. len + i - 1]

            go seed variants =
                let reqMask = randomListR seed (False, True)
                    req = applyMask reqMask indices
                in  request req $ \f' ->
                    let diff = f' - f
                        variants' = filter (variantFits reqMask diff) variants
                    in  (addToNext req .) $
                            unless (f' == n) $
                            case variants' of
                                [] -> error "No variants remained!"
                                [v] ->
                                    let req' = map fst . filter ((== 0) . snd) $ zip indices v
                                    in  -- trace ("Final in chunk, " ++ show v) $
                                        request req' $ \f'' ->
                                                         unless (f'' == n) $
                                                 process f'' (i + len)
                                vars -> go (snd $ random seed) vars
        in go 234234 initVariants

    variantFits mask diff variant =
        let view = applyMask mask variant
        in  diff == length view - 2 * (sum view)

    applyMask :: [Bool] -> [a] -> [a]
    applyMask m l = map snd . filter fst $ zip m l

    unless :: Bool -> InputOutput -> InputOutput
    unless False io = io
    unless True _   = const []

    buildVariants len = A.elems $ shuffle 2345 $ replicateM len [0, 1]
    buildVariantsDef = buildVariants chunkSize
    buildVariantsCached len = if len == 10 then buildVariantsDef else buildVariants len


test :: (Int -> InputOutput) -> [Int] -> IO ()
test solution initial = doTest initial $ solution (length initial)
  where
    doTest :: [Int] -> InputOutput -> IO ()
    doTest si sol = void . ST.stToIO . ST.fixST $ \input -> do
        string <- A.newListArray (1, length si) si :: ST.ST s (A.STArray s Int Int)
        let f = sum si
        let output = sol input
        fmap (sum si :) $ go 0 string f output
    go (k :: Int) s f (out : output) = do
        changes <- forM out $ \i -> do
            e <- A.readArray s i
            let e' = 1 - e
            A.writeArray s i e'
            return (e' - e)
        let f' = f + sum changes
        (f' : ) <$> go (k + 1) s f' output
    go k _ f [] =
        trace "Final:" $
        trace ("Iterations: " ++ show k) $
        trace ("Resulting fitness: " ++ show f) $
        return []

