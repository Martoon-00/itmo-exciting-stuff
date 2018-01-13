{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | ~3*n/4 solution of OneMax problem.

module Main where

import           Control.Monad         (forM, forM_, replicateM, void)
import           Data.IORef            (IORef, newIORef, readIORef, writeIORef)
import           Data.List             (group, sort)
import           Data.Word             (Word16)
import           GHC.IO.Unsafe         (unsafePerformIO)
import           Prelude               hiding (interact)
import           System.IO             (hClose, hFlush, stdin, stdout)
import           System.Random         (randomRIO)

import qualified Control.Monad.ST.Lazy as ST
import qualified Data.Array            as A
import qualified Data.Array.IO.Safe    as A
import qualified Data.Array.ST.Safe    as A
import qualified Data.Bits             as B
import qualified Data.Map              as M

import           Debug.Trace

main :: IO ()
main = interact $ map (unwords . map show) . process . map read . words
  where
    process (n:fs) = solve n fs
    process _      = error "not enought input"

-- For profiling
-- main :: IO ()
-- main = test solve =<< replicateM 100000 (randomRIO (0, 1))

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

dropSeed :: (Seed, a) -> a
dropSeed = snd

randomR :: Enum a => Seed -> (a, a) -> (Seed, a)
randomR s (l, r) =
    let (s', g) = random s
        i = (g `mod` (fromEnum r - fromEnum l + 1)) + fromEnum l
    in  (s', toEnum i)

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
request req f inpss = req : let (!inp:inps) = inpss in f inp inps

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
    in noMoreThan (limit n) . atLeastOneFlip $ process fi 1 fs
  where
    process !f i
        | i > n = expect f n
        | otherwise =
        let len = min chunkSize (n - i + 1)
            initVariants = buildInitVariantsCached len
            buildVariant v = map (+i) $ filter (B.testBit v) [0 .. len - 1]

            go seed path variants =
                let reqMask :: Word16 = head variants -- dropSeed $ randomR seed (1, variantsLast)
                    req = buildVariant reqMask
                in  request req $ \f' ->
                    let diff = f' - f
                        getVariantsCacheOr' = if len == chunkSize then getVariantsCacheOr else const id
                        variants' = -- (\x -> trace ("Variants: " ++ show (map buildVariant x)) x) $
                                    getVariantsCacheOr' (diff : path) $
                                    filter (variantFits reqMask diff) variants
                    in  (addToNext req .) $
                            -- unless (f' == n) $
                            case variants' of
                                [] -> error "No variants remained!"
                                [v] ->
                                    let req' = buildVariant $ B.complement v
                                    in  -- trace ("Final in chunk, " ++ show v) $
                                        request req' $ \f'' ->
                                            unless (f'' == n) $
                                                 process f'' (i + len)
                                vars -> go (dropSeed $ random seed) (diff : path) vars
        in go 2334234 [] initVariants

    buildInitVariants len =
        let variantsLast = 2 ^ len - 1
        in  (variantsLast :) $ A.elems . shuffle 232234 $
            [variantsLast - 1, variantsLast - 2 .. 0]
    buildInitVariantsDef = buildInitVariants chunkSize
    buildInitVariantsCached len = if len == chunkSize then buildInitVariantsDef else buildInitVariants len

    variantFits mask diff variant =
        let view = mask B..&. variant
        in  diff == B.popCount mask - 2 * (B.popCount view)

    unless :: Bool -> InputOutput -> InputOutput
    unless False io = io
    unless True _   = const []

variantsCache :: IORef (M.Map [Int] [Word16])
variantsCache = unsafePerformIO $ newIORef M.empty
{-# NOINLINE variantsCache #-}

getVariantsCacheOr :: [Int] -> [Word16] -> [Word16]
getVariantsCacheOr key value
    | length key > 3 = value
    | otherwise = unsafePerformIO $ do
        cache <- readIORef variantsCache
        case M.lookup key cache of
            Just x -> return x
            Nothing -> do
                writeIORef variantsCache $ M.insert key value cache
                return value

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

