-- | Primitives and combinators for writting probabilistic programs.

module ProbabolisticPrograms where

import qualified Graphics.Rendering.Chart.Backend.Diagrams as C
import qualified Graphics.Rendering.Chart.Easy             as C
import qualified Test.QuickCheck                           as Q
import           Universum                                 hiding (flip)
import           Unsafe                                    (unsafeHead)

type Prob = Double
type Distr a = [(Prob, a)]

flip :: Prob -> Q.Gen Bool
flip p = (p < ) <$> Q.choose (0, 1)

multinomial :: [(Int, Q.Gen a)] -> Q.Gen a
multinomial = Q.frequency

conditionally :: Q.Gen (Maybe a) -> Q.Gen a
conditionally = (`Q.suchThatMap` identity)

generate :: Q.Gen a -> IO a
generate = Q.generate

distribution :: Ord a => Int -> Q.Gen a -> Q.Gen (Distr a)
distribution k gen =
    normalize . map (length &&& unsafeHead) . group . sort <$>
    replicateM k gen
  where
    normalize l =
        let total = fromIntegral . sum $ map fst l
        in  map (first $ (/ total) . fromIntegral) l

histogram' :: Show a => FilePath -> Distr a -> IO ()
histogram' path distr = C.toFile C.def path $ do
    C.layout_title C..= "Histogram"
    C.layout_title_style . C.font_size C..= 10
    C.layout_x_axis . C.laxis_generate
        C..= C.autoIndexAxis (map (show . snd) distr)
    C.plot $ C.plotBars <$> C.bars [""] (C.addIndexes . map pure $ map fst distr)

histogram :: Show a => FilePath -> IO (Distr a) -> IO ()
histogram path mkDistr = histogram' path =<< mkDistr

-- * Examples

example1 :: Q.Gen Bool
example1 = conditionally $ do
    a <- flip 0.5
    b <- flip 0.5
    return $
        a <$
        guard (a || b)

example2 :: [Int] -> Q.Gen [Int]
example2 list = conditionally $ do
    sublist <- Q.sublistOf set
    return $ guard (sum subset == 1) $> subset
