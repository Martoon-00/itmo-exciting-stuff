-- | Primitives and combinators for writting probabilistic programs.

module ProbabolisticPrograms where

import qualified Graphics.Rendering.Chart.Backend.Diagrams as C
import qualified Graphics.Rendering.Chart.Easy             as C
import qualified Test.QuickCheck                           as Q
import qualified Test.QuickCheck.Gen                       as Q
import qualified Test.QuickCheck.Random                    as Q
import           Universum                                 hiding (flip, set)
import           Unsafe                                    (unsafeFromJust, unsafeHead)

-- | Probability, supposed to vary in [0, 1] range.
type Prob = Double

-- | Some built distribution.
type Distr a = [(Prob, a)]

-- | Invoke given QuickCheck generator, passing OS-provided seed.
generate :: Q.Gen a -> IO a
generate = Q.generate

-- | Invoke given generator, passing specified seed
-- (generators are deterministic).
generateDet :: Int -> Q.Gen a -> a
generateDet seed gen = Q.unGen gen (Q.mkQCGen seed) 30

-- | Generates 'True' with given probability.
flip :: Prob -> Q.Gen Bool
flip p = (p < ) <$> Q.choose (0, 1)

-- | Chooses one of given generators, with weighted random distribution.
multinomial :: [(Int, Q.Gen a)] -> Q.Gen a
multinomial = Q.frequency

-- | Repeat invoking given possibly failing generator for reasonable
-- amount of attemts, until failure.
conditionally :: Q.Gen (Maybe a) -> Q.Gen a
conditionally gen =
    maybe genFailed unsafeFromJust <$> gen `Q.suchThatMaybe` isJust
  where
    genFailed = error "Failed to generate value which fits condition"

-- | Modify number of attempts inner 'conditionally' performs before giving up.
adjust :: (Int -> Int) -> Q.Gen a -> Q.Gen a
adjust = Q.scale

-- | Builds distribution, invoking given generator specified number of times
-- and calculating frequency of each encountered value.
distribution :: Ord a => Int -> Q.Gen a -> Q.Gen (Distr a)
distribution k gen =
    normalize . map (length &&& unsafeHead) . group . sort <$>
    replicateM k gen
  where
    normalize l =
        let total = fromIntegral . sum $ map fst l
        in  map (first $ (/ total) . fromIntegral) l

-- | Draw diagram, and put generated file to given location.
-- I failed to find a way to display a window on spot :\
histogram :: Show a => FilePath -> IO (Distr a) -> IO ()
histogram path mkDistr = doBuild =<< mkDistr
  where
    doBuild distr = C.toFile C.def path $ do
        C.layout_title C..= "Histogram"
        C.layout_title_style . C.font_size C..= 10
        C.layout_x_axis . C.laxis_generate
            C..= C.autoIndexAxis (map (show . snd) distr)
        C.plot $ C.plotBars <$> C.bars [""] (C.addIndexes . map pure $ map fst distr)


-- * Examples

-- | Simple example with coin thrown.
example1 :: Q.Gen Bool
example1 = conditionally $ do
    a <- flip 0.5
    b <- flip 0.5
    return $
        a <$            -- return 'a'
        guard (a || b)  -- fail if (a || b) doesn't hold

-- | For given set of numbers, generates subset of sum 1.
--
-- Subset is selecting via choosing upon each value whether to choose it or not.
-- Number of generation attempts is slightly increased in advance, you can
-- increase more for difficult cases.
example2 :: [Int] -> Q.Gen [Int]
example2 set = adjust (* 10) . conditionally $ do
    subset <- Q.sublistOf set
    return $
        guard (sum subset == 1) $> subset
