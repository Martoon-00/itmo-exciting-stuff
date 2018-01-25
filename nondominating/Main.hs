{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE ViewPatterns     #-}

-- | Non-dominating sort of many-dimensional objects

module Main where

import           Control.Arrow            ((&&&))
import           Control.Monad            (forM, forM_, unless, when)
import           Control.Monad.Fix        (fix)
import qualified Control.Monad.ST         as ST
import           Control.Monad.State      (State, evalState, get, modify, put, runState)
import           Data.Bifunctor           (first, second)
import           Data.Function            (on)
import           Data.Maybe               (fromJust, fromMaybe)
import           Data.Monoid              (Sum (..))
import           Data.Monoid              ((<>))
import           Data.Ord                 (comparing)
import qualified Data.Set                 as S
import qualified Data.STRef.Strict        as ST
import           GHC.Exts                 (build)
import           Prelude

import qualified Data.List                as L
import qualified Data.Map.Strict          as M
import qualified Data.Vector              as V

import qualified Test.QuickCheck          as Q hiding (reason)
import qualified Test.QuickCheck.Gen      as Q
import qualified Test.QuickCheck.Property as Q
import qualified Test.QuickCheck.Random   as Q

import           Debug.Trace

main :: IO ()
main = interact $ (++ "\n") . unwords . map show . process . map read . words
  where
   process (n:d:coord) = solve sortSAC d $
                         map V.fromList . take n $ chunksOf d coord
   process _           = error "not enought input"

type Coord = Int
type Point = V.Vector Coord
type Rank = Word

-- * Utils

-- ** Median

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
    splitter ![] _ n = n
    splitter l c n   = l `c` splitter (drop i l) c n

-- ** Segment tree

data SegmentTreeStructure s k v m
    = Node (SegmentTreeStructure s k v m) (k -> Bool) (SegmentTreeStructure s k v m) (ST.STRef s m)
    | Leaf k (ST.STRef s (S.Set v))

data SegmentTree s k v m = SegmentTree
    { stStructure  :: SegmentTreeStructure s k v m
    , stGetKey     :: v -> k
    , stGetSummary :: S.Set v -> m
    }

mkSegTree
    :: forall s k v m.
       (Ord k, Monoid m)
    => (v -> k) -> (S.Set v -> m) -> [v] -> ST.ST s (SegmentTree s k v m)
mkSegTree stGetKey stGetSummary allValues = do
    stStructure <- go uniqKeys
    return SegmentTree{..}
  where
    uniqKeys = V.fromList . nubSeqBy id . L.sort $ map stGetKey allValues
    go keys
        | V.length keys == 0 = error "Can't make segment tree of no values"
        | V.length keys == 1 = Leaf (V.head keys) <$> ST.newSTRef S.empty
        | otherwise = do
              let med = V.length keys `div` 2
              mr <- ST.newSTRef mempty
              l <- go $ V.take med keys
              r <- go $ V.drop med keys
              let d = (< keys V.! med)
              return $ Node l d r mr

getSegElemSummary :: Monoid m => (S.Set v -> m) -> SegmentTreeStructure s k v m -> ST.ST s m
getSegElemSummary stGetSummary = \case
    Leaf _ setv -> stGetSummary <$> ST.readSTRef setv
    Node _ _ _ mr -> ST.readSTRef mr

updateSegTree :: Monoid m => k -> SegmentTree s k v m -> ST.ST s ()
updateSegTree k SegmentTree{..} = go stStructure
  where
    go = \case
        Leaf _ _ -> pure ()
        Node l d r mr -> do
            if d k then go l else go r
            mapM (getSegElemSummary stGetSummary) [l, r]
                >>= ST.writeSTRef mr . mconcat

modifySegTree
    :: Monoid m
    => k -> (S.Set v -> S.Set v) -> SegmentTree s k v m -> ST.ST s ()
modifySegTree k f st@SegmentTree{..} = do
    go stStructure
    updateSegTree k st
  where
    go = \case
        Leaf _ setv -> ST.modifySTRef setv f
        Node l d r _ ->
            if d k then go l else go r

insertSegTree :: (Monoid m, Ord v) => v -> SegmentTree s k v m -> ST.ST s ()
insertSegTree v st@SegmentTree{..} = modifySegTree (stGetKey v) (S.insert v) st

deleteSegTree :: (Monoid m, Ord v) => v -> SegmentTree s k v m -> ST.ST s ()
deleteSegTree v st@SegmentTree{..} = modifySegTree (stGetKey v) (S.delete v) st

-- | Request or range, inclusively.
requestSegTree :: (Monoid m, Bounded k, Ord k) => (k, k) -> SegmentTree s k v m -> ST.ST s m
requestSegTree range SegmentTree{..} = go range stStructure
  where
    go (keyL, keyR) = \case
        l@(Leaf k _) ->
            if keyL <= k && k <= keyR
            then getSegElemSummary stGetSummary l
            else pure mempty
        n@(Node l isLeft r _) ->
            if (keyL, keyR) == (minBound, maxBound)
                then getSegElemSummary stGetSummary n
            else if isLeft keyR
                then go (keyL, keyR) l
            else if not (isLeft keyL)
                then go (keyL, keyR) r
            else
                (<>) <$> go (keyL, maxBound) l <*> go (minBound, keyR) r

-- ** Utils

dominates :: Point -> Point -> Bool
dominates (V.toList -> p1) (V.toList -> p2) = and
    [ and $ zipWith (<=) p1 p2
    , or  $ zipWith (<)  p1 p2
    ]

nubSeqBy :: Eq b => (a -> b) -> [a] -> [a]
nubSeqBy cmp = map head . L.groupBy ((==) `on` cmp)

noChanges :: State s a -> State s a
noChanges state = get >>= \s -> state <* put s

data Lens s a = Lens { getter :: s -> a, setter :: a -> s -> s }

_1 :: Lens (a, b) a
_1 = Lens fst (first . const)

_2 :: Lens (a, b) b
_2 = Lens snd (second . const)

zoom :: Lens s1 s2 -> State s2 a -> State s1 a
zoom lens state = do
    s <- get
    let (a, s') = runState state (getter lens s)
    modify (setter lens s') *> pure a

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

updateRankIfNotKnown :: Rank -> (PointMeta -> PointMeta)
updateRankIfNotKnown r m
    | metaForAnswer m = m { metaRank = max r (metaRank m) }
    | otherwise = m

type PartialDominance = Bool

type RankedPoints = V.Vector (Point, Rank)

type Solver
     = V.Vector (Point, Rank)  -- ^ known ranks
    -> V.Vector (Point, Rank)  -- ^ request
    -> V.Vector (Point, Rank)  -- ^ updated request points

sortDumb :: RankedPoints -> RankedPoints
sortDumb = updateDumb V.empty

updateDumb :: RankedPoints -> RankedPoints -> RankedPoints
updateDumb (V.toList -> known) (V.toList -> request) =
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

data SortMode
    = LoopMode (V.Vector (Point, Rank))
    | UpdateMode (V.Vector (Point, Rank)) (V.Vector (Point, Rank))

type LineState = State (M.Map (Coord, Rank) PointMeta, M.Map Rank PointMeta)

sortSweepLine :: SortMode -> V.Vector (Point, Rank)
sortSweepLine = \case
    LoopMode (V.toList -> request) -> V.fromList $
        let points = map (toLineEntry True) request
            sortedPoints = lexSort points
            result = runSweepLine $ mapM loopSweepLine sortedPoints
        in  map fromLineEntry result
    UpdateMode (V.toList -> known) (V.toList -> request) -> V.fromList $
        let allPoints = map (toLineEntry False) known
                     ++ map (toLineEntry True) request
            sortedPoints = lexSort allPoints
            updated = runSweepLine $ mapM updatingSweepLine sortedPoints
        in  map fromLineEntry $ filter metaForAnswer updated
  where
    getX = (V.! 0)
    getY = (V.! 1)
    getMetaY PointMeta{..} = getY metaPoint
    getLineKeyNoRank = (, maxBound) . getMetaY
    lexSort = L.sortBy (comparing $ (getX &&& getY) . metaPoint)
    runSweepLine :: State (M.Map k v, M.Map k2 v2) a -> a
    runSweepLine = flip evalState (M.empty, M.empty)

    insert getLineKey meta = do
        modify . first $ M.insert (getLineKey meta) meta
        modify . second $ M.insert (metaRank meta) meta

    delete getLineKey meta = do
        modify . first $ M.delete (getLineKey meta)
        modify . second $ M.delete (metaRank meta)

    -- | For given request points, update ranks.
    -- Here and below, line is stored as map from Y coordinate to the point.
    -- If there were several points with same Y (and sequencial ranks),
    -- we keep one with the highies rank.
    loopSweepLine :: PointMeta -> LineState PointMeta
    loopSweepLine = processRequestPoint getLineKeyNoRank

    -- | For given known and request points, put known on line and
    -- update ranks of request points.
    updatingSweepLine :: PointMeta -> LineState PointMeta
    updatingSweepLine meta =
        if metaForAnswer meta
        then noChanges $ processRequestPoint getLineKeyNoRank meta
        else processKnownPoint (getMetaY &&& metaRank) meta

    processKnownPoint getLineKey meta = do
        (_, front) <- get
        let rank = metaRank meta
        case M.lookup rank front of
            Nothing ->
                -- trace ("Inserting known point " ++ show meta) $
                insert getLineKey meta
            Just oldMeta | getLineKey oldMeta > getLineKey meta -> do
                -- trace ("Replacing known point with " ++ show meta) $ do
                delete getLineKey oldMeta
                insert getLineKey meta
            Just _ -> return ()
        return meta

    processRequestPoint :: (PointMeta -> (Coord, Rank)) -> PointMeta -> LineState PointMeta
    processRequestPoint getLineKey meta = do
        unless (metaForAnswer meta) $ error "Only request points here"
        let key = getLineKey meta
        (line, _) <- get
        case M.lookupGT key line of
            Nothing           -> insertPointAtTop getLineKey meta
            Just (_, oldMeta) -> lowerPoint getLineKey oldMeta meta

    getMaxFrontRank front =
        fromMaybe 0 $ (+1) . metaRank . fst <$> M.maxView front

    insertPointAtTop getLineKey meta = do
        (_, front) <- get
        let maxRank = getMaxFrontRank front
        let newMeta = updateRankIfNotKnown maxRank meta
        insert getLineKey newMeta
        !_ <- traceM ("Inserting " ++ show newMeta)
        return newMeta
    lowerPoint :: (PointMeta -> (Coord, Rank)) -> PointMeta -> PointMeta -> LineState PointMeta
    lowerPoint getLineKey oldMeta meta = do
        let key = getLineKey meta
        (line, front) <- get
        let belowRank = metaRank . snd <$> M.lookupLE key line
        let newRank = maybe 0 (+1) belowRank
        -- update line
        when (newRank == metaRank oldMeta) $
            delete getLineKey $ (\(Just x) -> x) $ M.lookup newRank front
        let newMeta = updateRankIfNotKnown newRank meta
        insert getLineKey newMeta
        !_ <- traceM ("Replacing " ++ show oldMeta ++ " with " ++ show newMeta)
        return newMeta

sortSAC
    :: Int                    -- ^ current dimension
    -> RankedPoints
    -> RankedPoints
sortSAC 0 _ = error "Too difficult"
sortSAC 1 _ = error "Dunno how to work for 1-dim"
sortSAC 2 points = sortSweepLine (LoopMode points)
sortSAC d points   -- TODO: extended base
    | length points <= 1 = points
    | otherwise =
        let med = findMed id $ fmap (getCoord . fst) points  -- TODO: try no decorate?
            comparingToMed (p, _) = getCoord p `compare` med
            (pointsL, pointsM, pointsR) = split comparingToMed points
            !_ = trace ("loop split " ++ show (pointsL, pointsM, pointsR)) ()

            sortedL = sortSAC d pointsL
            !_ = trace ("loop sortedL: " ++ show sortedL) ()
            sortedM = sortSAC (d - 1) $
                      updateSAC d sortedL pointsM
            !_ = trace ("loop sortedM: " ++ show sortedM) ()
            sortedR = sortSAC d $
                      updateSAC d (sortedL <> sortedM) pointsR
            !_ = trace ("loop sortedR: " ++ show sortedR) ()
        in  mconcat [sortedL, sortedM, sortedR]
  where
    getCoord = (V.! (d - 1))

updateSAC
    :: Int                    -- ^ current dimension
    -> RankedPoints
    -> RankedPoints
    -> RankedPoints
updateSAC 0 _ _ = error "Too difficult"
updateSAC 1 _ _ = error "Dunno how to work for 1-dim"
updateSAC 2 known req = sortSweepLine (UpdateMode known req)
updateSAC d known req   -- TODO: extended base
    | length req == 0 =
        V.empty
    | length req == 1 =
        let [(req1, rank)] = V.toList req
            newRank = maximum . (rank :) . map (succ . snd) $
                      filter ((`dominates` req1) . fst) $
                      V.toList known
        in  V.singleton (req1, newRank)
    | otherwise =
        let med = findMed id $ fmap (getCoord . fst) req  -- TODO: try no decorate?
            comparingToMed (p, _) = getCoord p `compare` med
            (knownL, knownM, knownR) = split comparingToMed known
            (reqL, reqM, reqR) = split comparingToMed req

            !_ = trace ("Updating over " ++ show known) ()

            sortedL = updateSAC d knownL reqL
            !_ = trace ("update sortedL: " ++ show sortedL) ()
            sortedM = updateSAC (d - 1) knownM $
                      updateSAC (d - 1) knownL reqM
            !_ = trace ("update sortedM: " ++ show sortedM) ()
            sortedR = updateSAC d knownR $
                      updateSAC d (knownL <> knownM) reqR
            !_ = trace ("update sortedR: " ++ show sortedR) ()
        in  mconcat [sortedL, sortedM, sortedR]
  where
    getCoord = (V.! (d - 1))

solve :: (Int -> RankedPoints -> RankedPoints) -> Int -> [Point] -> [Rank]
solve solver d points =
    let order = M.fromListWith mappend $ zip points $ map (\x -> [x]) [1 :: Int ..]
        getOrder p = fromJust $ M.lookup p order
        pointsNoDups = nubSeqBy id $ L.sort points
        request = V.fromList $ map (, 0) $ pointsNoDups
        answer = V.toList $ solver d request
    in  map snd . nubSeqBy fst . L.sortOn fst $
        [ (id', rank)
        | (point, rank) <- answer
        , id' <- getOrder point
        ]

testSegTree :: Maybe Int -> IO ()
testSegTree seed = Q.quickCheckWith args $
    Q.forAll (Q.resize 20 $ Q.listOf1 $ (,) <$> Q.choose (-5, 5) <*> Q.choose (0, 10)) $
        \((nubSeqBy id . L.sort -> input) :: [(Int, Word)]) ->
    Q.forAll (Q.sublistOf input `Q.suchThat` (not . null)) $
        \(toAdd :: [(Int, Word)]) ->
    Q.forAll (fmap pure $ Q.resize 7 Q.arbitrary `Q.suchThat` \(l, r) -> l <= r) $
        \(toRequest :: [(Int, Int)]) ->
    let segAns = runWithSegTree input toAdd toRequest
        dumbAns = runDumb toAdd toRequest
    in  if segAns == dumbAns
        then Q.succeeded
        else Q.failed
             { Q.reason = "Expected " ++ show dumbAns ++ ", got " ++ show segAns }
  where
    args =
        Q.stdArgs
        { Q.replay = fmap (\s -> (Q.mkQCGen s, s)) seed
        , Q.maxSuccess = 10000
        }
    runDumb :: [(Int, Word)] -> [(Int, Int)] -> [Word]
    runDumb present =
        map $ \(reqL, reqR) -> sum . map snd $ filter (\(x, _) -> reqL <= x && x <= reqR) present
    runWithSegTree input toAdd toRequest = ST.runST $ do
        tree <- mkSegTree fst (foldMap (Sum . snd)) input
        forM_ toAdd $ \added -> insertSegTree added tree
        forM toRequest $ \req -> getSum <$> requestSegTree req tree

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
    let ans = solve sortSAC d points
        ans' = solve (\_d -> sortDumb) d points
    unless (ans == ans') $
        Left $ "Bad answer, got " ++ show ans ++ ", expected " ++ show ans'

test :: Maybe Int -> Int -> Int -> IO ()
test seed d n = Q.quickCheckWith args $ Q.forAll (genInput d n) $ \input ->
    trace "\n\n" $
    case check d input of
        Left err -> Q.failed{ Q.reason = err }
        Right () -> Q.succeeded
  where
    args =
        Q.stdArgs
        { Q.replay = fmap (\s -> (Q.mkQCGen s, s)) seed
        , Q.maxSuccess = 10000
        }
