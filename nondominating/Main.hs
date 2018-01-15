{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE ViewPatterns    #-}

-- | Non-dominating sort of many-dimensional objects

module Main where

import           Control.Arrow              ((&&&))
import           Control.Monad              (unless)
import           Control.Monad.Fix          (fix)
import           Control.Monad.State.Strict (State, evalState, get, modify)
import           Data.Function              (on)
import           Data.Maybe                 (fromJust, fromMaybe)
import           Data.Ord                   (comparing)
import           GHC.Exts                   (build)
import           Prelude

import qualified Data.List                  as L
import qualified Data.Map.Strict            as M
import qualified Data.Vector                as V

import qualified Test.QuickCheck            as Q hiding (reason)
import qualified Test.QuickCheck.Gen        as Q
import qualified Test.QuickCheck.Property   as Q
import qualified Test.QuickCheck.Random     as Q

import           Debug.Trace

main :: IO ()
main = interact $ (++ "\n") . unwords . map show . process . map read . words
  where
   process (n:d:coord) = solve sortSplitAndConquer d $
                         map V.fromList . take n $ chunksOf d coord
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
    } deriving (Show)

toLineEntry :: Bool -> (Point, Rank) -> PointMeta
toLineEntry a (p, r) = PointMeta p r a

fromLineEntry :: PointMeta -> (Point, Rank)
fromLineEntry (PointMeta p r _) = (p, r)

updateRank :: (Rank -> Rank) -> (PointMeta -> PointMeta)
updateRank f m = m { metaRank = f (metaRank m) }

type Solver
     = V.Vector (Point, Rank)  -- ^ known ranks
    -> V.Vector (Point, Rank)  -- ^ request
    -> V.Vector (Point, Rank)  -- ^ updated request points

sortDumb :: Solver
sortDumb (V.toList -> known) (V.toList -> request) =
    V.fromList . fix $ \newRequestPoints ->
        flip map request $ \(me, myRank) ->
            let allPoints = known ++ newRequestPoints
                dominators = filter ((`dominates` me) . fst) allPoints
                newRank = case dominators of
                    [] -> 0
                    ds -> maximum (map snd ds) + 1
            in (me, max myRank newRank)

-- | 'True' if point is part of request, `False` if it is known.
-- Since points from request are always greater than known points
-- at least in one coordinate, if in 'sortSweepLine' we encounter
-- request point with X and Y the same as for some known point,
-- then that known dominates the request point due to some other coordinate,
-- (but there is no domination for reqest-reqest and known-known points pairs).
-- This type helps to set known points in VIP position.
newtype Interest = Interest { getInterest :: Bool }
    deriving (Eq, Ord, Show)

sortSweepLine :: Solver
sortSweepLine (V.toList -> known) (V.toList -> request) =
    let allPoints = map (toLineEntry False) known
                 ++ map (toLineEntry True) request
        sortedPoints = L.sortBy (comparing $ (getX &&& getY) . metaPoint) allPoints
    in  V.fromList . map fromLineEntry . filter metaForAnswer $
        flip evalState M.empty $ mapM sweepLine sortedPoints
  where
    getX = (V.! 0)
    getY = (V.! 1)
    getLineKey PointMeta{..} = (getY metaPoint, Interest metaForAnswer)
    sweepLine :: PointMeta -> State (M.Map (Int, Interest) PointMeta) PointMeta
    sweepLine meta = do
        let key = getLineKey meta
        line <- traceShowId <$> get
        case M.lookupGT key line of
            Nothing -> do
                let maxRank = fromMaybe 0 $ (+1) . metaRank . fst <$> M.maxView line
                let newMeta = updateRank (max maxRank) meta
                modify $ M.insert key newMeta
                return newMeta
            Just (oldY, oldMeta) -> do
                let newMeta = updateRank (max (metaRank oldMeta)) meta
                modify $ M.insert key newMeta
                       . M.delete oldY
                return newMeta

sortSplitAndConquer
    :: Int                    -- ^ current dimension
    -> Solver
sortSplitAndConquer 0 _ _ = error "Too difficult"
sortSplitAndConquer 1 _ _ = error "Dunno how to work for 1-dim"
sortSplitAndConquer 2 known req = sortSweepLine known req
sortSplitAndConquer d known req   -- TODO: extended base
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
            (reqL, reqM, reqR) = split comparingToMed req

            sortedL = sortSplitAndConquer d knownL reqL
            -- !_ = trace ("sortedL: " ++ show sortedL) 0
            sortedM = sortSplitAndConquer (d - 1) (mconcat [knownL, sortedL]) $
                      sortSplitAndConquer (d - 1) sortedL reqM
            -- !_ = trace ("sortedM: " ++ show sortedM) 0
            sortedR = sortSplitAndConquer (d - 1) (mconcat [knownL, knownM, sortedL, sortedM]) $
                      sortSplitAndConquer d knownR reqR
            -- !_ = trace ("sortedR: " ++ show sortedR) 0
        in  mconcat [sortedL, sortedM, sortedR]
  where
    getCoord = (V.! (d - 1))

solve :: (Int -> Solver) -> Int -> [Point] -> [Rank]
solve solver d points =
    let order = M.fromListWith mappend $ zip points $ map (\x -> [x]) [1 :: Int ..]
        getOrder p = fromJust $ M.lookup p order
        pointsNoDups = nubSeqBy id $ L.sort points
        request = V.fromList $ map (, 0) $ pointsNoDups
        answer = V.toList $ solver d V.empty request
    in  map snd . nubSeqBy fst . L.sortOn fst $
        [ (id', rank)
        | (point, rank) <- answer
        , id' <- getOrder point
        ]

genInput :: Int -> Int -> Q.Gen [Point]
genInput d pointsNum =
    Q.vectorOf pointsNum .
        fmap V.fromList . Q.vectorOf d $
        Q.resize 10 $ Q.getNonNegative <$> Q.arbitrary

-- | Invoke given generator, passing specified seed
-- (generators are deterministic).
generateDet :: Int -> Q.Gen a -> a
generateDet seed gen = Q.unGen gen (Q.mkQCGen seed) 10

check :: Int -> [Point] -> Either String ()
check d points = do
    let ans = solve sortSplitAndConquer d points
        ans' = solve (\_d -> sortDumb) d points
    unless (ans == ans') $
        Left $ "Bad answer, got " ++ show ans ++ ", expected " ++ show ans'

test :: Maybe Int -> Int -> Int -> IO ()
test seed d n = Q.quickCheckWith args $ Q.forAll (genInput d n) $ \input ->
    trace "" $
    case check d input of
        Left err -> Q.failed{ Q.reason = err }
        Right () -> Q.succeeded
  where
    args = Q.stdArgs{ Q.replay = fmap (\s -> (Q.mkQCGen s, s)) seed }
