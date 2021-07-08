{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Foldable (foldl', traverse_)
import Data.Monoid (Sum(..))

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Transducers

default (Int)

prop_reducer :: (Eq b, Show b) => Reducer a b -> ([a] -> b) -> [a] -> Property
prop_reducer f g ls = reduce f ls === g ls

prop_transducer :: (Eq b, Show b) => Transducer a b -> ([a] -> [b]) -> [a] -> Property
prop_transducer f g ls = transduce f intoList ls === g ls

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x : _) = Just x

lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe [x] = Just x
lastMaybe (_ : xs) = lastMaybe xs

minimumMaybe :: (Ord a) => [a] -> Maybe a
minimumMaybe [] = Nothing
minimumMaybe xs = Just (minimum xs)

maximumMaybe :: (Ord a) => [a] -> Maybe a
maximumMaybe [] = Nothing
maximumMaybe xs = Just (maximum xs)

foldl'1 :: (a -> a -> a) -> [a] -> Maybe a
foldl'1 _ [] = Nothing
foldl'1 f (x : xs) = Just $! foldl' f x xs

main :: IO ()
main = hspec $ do
    describe "reducers" $ do
        prop "intoLength" $ prop_reducer intoLength length
        prop "intoNull" $ prop_reducer intoNull null
        prop "intoList" $ prop_reducer intoList id
        prop "intoRevList" $ prop_reducer intoRevList reverse
        prop "intoSum" $ prop_reducer intoSum sum
        prop "intoProduct" $ prop_reducer intoProduct product
        prop "intoFirst" $ prop_reducer intoFirst headMaybe
        prop "intoLast" $ prop_reducer intoLast lastMaybe
        prop "intoAnd" $ prop_reducer intoAnd and
        prop "intoOr" $ prop_reducer intoOr or
        prop "intoAll" $ \(Fn f) -> prop_reducer (intoAll f) (all f)
        prop "intoAny" $ \(Fn f) -> prop_reducer (intoAny f) (any f)
        prop "intoMinimum" $ prop_reducer intoMinimum minimumMaybe
        prop "intoMaximum" $ prop_reducer intoMaximum maximumMaybe
        prop "intoMinimumBy" $ prop_reducer (intoMinimumBy compare) minimumMaybe
        prop "intoMaximumBy" $ prop_reducer (intoMaximumBy compare) maximumMaybe
        prop "intoMonoid" $ prop_reducer intoMonoid (mconcat :: [[Int]] -> [Int]) -- use Monoid [Int]
        prop "intoFoldMap" $ prop_reducer (intoFoldMap Sum getSum) (getSum . foldMap Sum) -- use Monoid (Sum Int)
        prop "intoFold" $ prop_reducer (intoFold (+) 0) (foldl' (+) 0)
        prop "intoFold1" $ prop_reducer (intoFold1 (+)) (foldl'1 (+))
        prop "intoFor_" $ \(Fn (f :: Int -> Maybe Int)) -> prop_reducer (intoFor_ f) (traverse_ f) -- use Applicative Maybe

    describe "transducers" $ do
        prop "mapping" $ \(Fn f) -> prop_transducer (mapping f) (map f)
        prop "filtering" $ \(Fn f) -> prop_transducer (filtering f) (filter f)
        prop "concatMapping" $ \(Fn f) -> prop_transducer (concatMapping f) (concatMap f)
        prop "taking" $ \n -> prop_transducer (taking n) (take n)
        prop "takingWhile" $ \(Fn f) -> prop_transducer (takingWhile f) (takeWhile f)
        prop "dropping" $ \n -> prop_transducer (dropping n) (drop n)
        prop "droppingWhile" $ \(Fn f) -> prop_transducer (droppingWhile f) (dropWhile f)
        prop "enumerating" $ prop_transducer enumerating (zip [0..])
        prop "postscanning" $ prop_transducer (postscanning intoSum) (tail . scanl (+) 0)
        prop "prescanning" $ prop_transducer (prescanning intoSum) (init . scanl (+) 0)
