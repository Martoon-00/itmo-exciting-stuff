{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}

-- | Non-dominating sort of many-dimensional objects

module Main where

import           Control.Monad.State.Strict (State, evalState, get, modify)
import           Data.Bifunctor             (first)
import           Data.Maybe                 (fromJust)
import           Data.Ord                   (comparing)
import           GHC.Exts                   (build)
import           Prelude

import qualified Data.List                  as L
import qualified Data.Map.Strict            as M
import qualified Data.Vector                as V

main :: IO ()
main = interact $ unwords . map show . process . map read . words
  where
    process (n:d:coord) = solve d (map V.fromList . take n $ chunksOf d coord)
    process _           = error "not enought input"

type Point = V.Vector Int
type Rank = Int

-- * Utils

splitOnMed :: Ord b => (a -> b) -> V.Vector a -> (V.Vector a, V.Vector a, V.Vector a)
splitOnMed cmp v =
    let med = findMed cmp v
        comp = comparing cmp
    in  split (`comp` med) v

findMed :: Ord b => (a -> b) -> V.Vector a -> a
findMed cmp v = findKth cmp v (V.length v `div` 2)

findKth :: Ord b => (a -> b) -> V.Vector a -> Int -> a
findKth cmp v k =
        let pivot  = findMedMed cmp $ V.toList v
            (l, _, r) = split (\x -> comparing cmp x pivot) v
        in  select l r pivot
  where
     select l r pivot
        | k < V.length l              = findKth cmp l k
        | k < V.length v - V.length r = pivot
        | otherwise                   =
            findKth cmp r $ k - (V.length v - V.length r)

findMedMed :: Ord b => (a -> b) -> [a] -> a
findMedMed _   []     = error "findMedMed: empty list"
findMedMed cmp xs
    | not (null $ drop 25 xs) = plainMed xs
    | otherwise = findMedMed cmp $ plainMed <$> chunksOf 5 xs
  where
    plainMed v = plainSort v !! (length v `div` 2)
    plainSort = L.sortBy (comparing cmp)

split :: (a -> Ordering) -> V.Vector a -> (V.Vector a, V.Vector a, V.Vector a)
split f v = ( extract LT, extract EQ, extract GT )
  where
    extract ord = V.filter (\x -> f x == ord) v

chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = map (take i) (build (splitter ls)) where
    splitter :: [e] -> ([e] -> a -> a) -> a -> a
    splitter [] _ n = n
    splitter l c n  = l `c` splitter (drop i l) c n

dominates :: Point -> Point -> Bool
dominates (V.toList -> p1) (V.toList -> p2) = and
    [ and $ zipWith (<=) p1 p2
    , or  $ zipWith (<)  p1 p2
    ]

-- * Solution

data PointMeta = PointMeta
    { metaPoint     :: Point
    , metaRank      :: Rank
    , metaForAnswer :: Bool
    }

updateRank :: (Rank -> Rank) -> (PointMeta -> PointMeta)
updateRank f m = m { metaRank = f (metaRank m) }

sortSweepLine :: [(Point, Rank)] -> [(Point, Rank)] -> [(Point, Rank)]
sortSweepLine known request =
    let toLineEntry a (p, r) = PointMeta p r a
        fromLineEntry (PointMeta p r _) = (p, r)
        allPoints = map (toLineEntry False) known
                 ++ map (toLineEntry True) request
        sortedPoints = L.sortBy (comparing $ getX . metaPoint) allPoints
    in  map fromLineEntry . filter metaForAnswer $
        flip evalState M.empty $ mapM sweepLine sortedPoints
  where
    getX = (V.! 1)
    getY = (V.! 2)
    sweepLine :: PointMeta -> State (M.Map Int PointMeta) PointMeta
    sweepLine meta = do
        let y = getY (metaPoint meta)
        line <- get
        case M.lookupGT y line of -- TODO: E?
            Nothing -> do
                let newMeta = updateRank (max (M.size line)) meta
                modify $ M.insert y newMeta
                return newMeta
            Just (oldY, oldMeta) -> do
                let newMeta = updateRank (max (metaRank oldMeta)) meta
                modify $ M.insert y newMeta
                       . M.delete oldY
                return newMeta

sortSplitAndConquer
    :: Int                    -- current dimension
    -> V.Vector (Point, Rank) -- known ranks
    -> V.Vector (Point, Rank) -- request
    -> V.Vector (Point, Rank) -- updated ranks of requested points
sortSplitAndConquer 0 _ _ = error "Too difficult"
sortSplitAndConquer 1 _ _ = error "Dunno how to work for 1-dim"
sortSplitAndConquer 2 known req = V.fromList $ sortSweepLine (V.toList known) (V.toList req)
sortSplitAndConquer d known req   -- TODO: extended base
    | otherwise =
        let med = findMed getCoord $ fmap fst req  -- TODO: try no decorate?
            (knownL, knownM, knownR) = split ((`compare` med) . fst) known
            (reqL, reqM, reqR) = split ((`compare` med) . fst) req

            sortedL = sortSplitAndConquer d knownL reqL
            sortedM = sortSplitAndConquer (d - 1) (mconcat [knownL, knownM, sortedL]) reqM
            sortedR = sortSplitAndConquer (d - 1) (mconcat [knownL, knownM, sortedL, sortedM]) $
                      sortSplitAndConquer d knownR reqR
        in  mconcat [sortedL, sortedM, sortedR]
  where
    getCoord = (V.! d)

solve :: Int -> [Point] -> [Rank]
solve d points =
    let order = M.fromList $ zip points [1 :: Int ..]
        getOrder p = fromJust $ M.lookup p order
        request = V.fromList $ map (, 0) points
        answer = V.toList $ sortSplitAndConquer d V.empty request
    in  map snd . L.sortOn fst $ map (first getOrder) answer
