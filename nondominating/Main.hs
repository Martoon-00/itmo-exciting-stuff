{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}

-- | Non-dominating sort of many-dimensional objects

module Main where

import           Control.Arrow              ((&&&))
import           Control.Monad.State.Strict (State, evalState, get, modify)
import           Data.Function              (on)
import           Data.Maybe                 (fromJust)
import           Data.Ord                   (Down (..), comparing)
import           GHC.Exts                   (build)
import           Prelude

import qualified Data.List                  as L
import qualified Data.Map.Strict            as M
import qualified Data.Vector                as V

import           Debug.Trace

main :: IO ()
main = interact $ (++ "\n") . unwords . map show . process . map read . words
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
    | null (drop 25 xs) = plainMed xs
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

nubSeqBy :: Eq b => (a -> b) -> [a] -> [a]
nubSeqBy cmp = map head . L.groupBy ((==) `on` cmp)

-- * Solution

data PointMeta = PointMeta
    { metaPoint     :: Point
    , metaRank      :: Rank
    , metaForAnswer :: Bool
    }

-- | Whether, considering reduced set of coordinates, equality of
-- some coordinate is allowed.
data Dominance
    = NoDominance    -- ^ domination is determined on usual rules
    | PartDominance  -- ^ one of sets dominates another one except cases of coordinates total match
    | TotalDominance -- ^ one of sets dominates another
    deriving (Eq, Ord, Enum)

nextDom :: Dominance -> Dominance
nextDom = toEnum . succ . fromEnum

updateRank :: (Rank -> Rank) -> (PointMeta -> PointMeta)
updateRank f m = m { metaRank = f (metaRank m) }


sortSweepLine :: Dominance -> [(Point, Rank)] -> [(Point, Rank)] -> [(Point, Rank)]
sortSweepLine TotalDominance _ _ = undefined -- sortFullDominance known request
sortSweepLine dominance known request =
    let toLineEntry a (p, r) = PointMeta p r a
        fromLineEntry (PointMeta p r _) = (p, r)
        allPoints = map (toLineEntry False) known
                 ++ map (toLineEntry True) request
        sortedPoints = L.sortBy (comparing $ (getX &&& Down . getY) . metaPoint) allPoints
    in  map fromLineEntry . filter metaForAnswer $
        flip evalState M.empty $ mapM sweepLine sortedPoints
  where
    getX = (V.! 0)
    getY = (V.! 1)
    lineLookup =
        case dominance of
            NoDominance   -> M.lookupGE
            PartDominance -> M.lookupGT
            _             -> error "Unexpected TotalDominance"
    sweepLine :: PointMeta -> State (M.Map Int PointMeta) PointMeta
    sweepLine meta = do
        let y = getY (metaPoint meta)
        line <- get
        case lineLookup y line of
            Nothing -> do
                let newMeta = updateRank (max (M.size line)) meta  -- TODO: what if known?
                modify $ M.insert y newMeta
                return newMeta
            Just (oldY, oldMeta) -> do
                let newMeta = updateRank (max (metaRank oldMeta)) meta
                modify $ M.insert y newMeta
                       . M.delete oldY
                return newMeta

sortSplitAndConquer
    :: Dominance
    -> Int                    -- ^ current dimension
    -> V.Vector (Point, Rank) -- ^ known ranks
    -> V.Vector (Point, Rank) -- ^ request
    -> V.Vector (Point, Rank) -- ^ updated ranks of requested points
sortSplitAndConquer _ 0 _ _ = error "Too difficult"
sortSplitAndConquer _ 1 _ _ = error "Dunno how to work for 1-dim"
sortSplitAndConquer t 2 known req = V.fromList $ sortSweepLine t (V.toList known) (V.toList req)
sortSplitAndConquer t d known req   -- TODO: extended base
    | length req == 0 =
        V.empty
    | length req == 1 =
        let [(req1, rank)] = V.toList req
            newRank = maximum . (rank :) . map snd $
                      filter ((`dominates` req1) . fst) $
                      V.toList known
        in  V.singleton (req1, newRank)
    | otherwise =
        let med = findMed id $ fmap (getCoord . fst) req  -- TODO: try no decorate?
            comparingToMed (p, _) = getCoord p `compare` med
            (knownL, knownM, knownR) = split comparingToMed known
            (reqL, reqM, reqR) = traceShowId $ split comparingToMed req

            sortedL = sortSplitAndConquer (nextDom t) d knownL reqL
            -- !_ = trace ("sortedL: " ++ show sortedL) 0
            sortedM = sortSplitAndConquer t (d - 1) (mconcat [knownL, sortedL]) $
                      sortSplitAndConquer (nextDom t) (d - 1) sortedL reqM
            -- !_ = trace ("sortedM: " ++ show sortedM) 0
            sortedR = sortSplitAndConquer t (d - 1) (mconcat [knownL, knownM, sortedL, sortedM]) $
                      sortSplitAndConquer (nextDom t) d knownR reqR
            -- !_ = trace ("sortedR: " ++ show sortedR) 0
        in  mconcat [sortedL, sortedM, sortedR]
  where
    getCoord = (V.! (d - 1))

solve :: Int -> [Point] -> [Rank]
solve d points =
    let order = M.fromListWith mappend $ zip points $ map (\x -> [x]) [1 :: Int ..]
        getOrder p = fromJust $ M.lookup p order
        request = V.fromList $ map (, 0) points
        answer = V.toList $ sortSplitAndConquer NoDominance d V.empty request
    in  map snd . nubSeqBy fst . L.sortOn fst $
        [ (id', rank)
        | (point, rank) <- answer
        , id' <- getOrder point
        ]
