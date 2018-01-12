{-# LANGUAGE BangPatterns #-}

-- | ~3*n/4 solution of OneMax problem.

module Main where

import           Control.Monad      (forM_)
import           Prelude            hiding (interact)
import           System.IO          (hClose, hFlush, stdin, stdout)

import qualified Data.Array         as A
import qualified Data.Array.MArray  as A
import qualified Data.Array.ST.Safe as A

main :: IO ()
main = interact $ map (unwords . map show) . process . map read . words
  where
    process (n:fs) = map (confuse' n) $ solve n fs
    process _      = error "not enought input"

    confuse' = confuse 234235652

interact :: (String -> [String]) -> IO ()
interact f = do
    input <- getContents
    forM_ (f input) $ \line -> putStrLn line >> hFlush stdout
    mapM_ hClose [stdout, stdin]

type Fitness = Int
type Flips = [Int]
type InputOutput = [Fitness] -> [Flips]

genPermutation :: Int -> Int -> A.Array Int Int
genPermutation seed n = A.runSTArray $ do
    array <- A.newListArray (1, n) [1..n]
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

solve :: Int -> InputOutput
solve n inps = let (fi:fs) = inps in atLeastOneFlip $ go fi n fs
  where
    go _ 0 =
        -- found solution
        const []
    go fl 1
        -- check whether last element should be flipped
        | fl == n = const []
        | otherwise = const [[1]]
    go !fl k =
        -- try to flip next 2 and see what happens
        let b1 = k
            b2 = k - 1
        in  request [b1, b2] $ \f ->
            case f - fl of
                -- entire profit - go further
                2  -> go f (k - 2)
                -- entire loss - flip those back on next request
                -2 -> addToNext [b1, b2] . go fl (k - 2)
                -- check which of the two gives profit
                0  -> request [b2] $ \f2 ->
                    case f2 - fl of
                        -- optimized - go further
                        1  -> go f2 (k - 2)
                        -- made worse, fix on next iteration
                        -1 -> addToNext [b1, b2] . go (fl + 1) (k - 2)
                        o  -> error ("got fitness diff " ++ show o ++ "??")
                o  -> error ("got fitness diff " ++ show o ++ "?")
