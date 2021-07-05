{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

{- |
Transducers are composable algorithmic transformations.

= Naming convention

Reducers are prefixed with "into" (e.g. 'intoSum'), while transducers have an "ing" suffix (e.g. 'mapping').

= See also

* https://clojure.org/reference/transducers
* https://hypirion.com/musings/haskell-transducers
-}

module Transducers
    ( Reduced(Reduced), continue, reduced, getReduced
    , Reducer(..), reducer, reducer_
    , Transducer
    , reduce, transduce
    -- * Reducers
    , intoList, intoRevList
    , intoLength
    , intoNull
    , intoElem
    , intoSum, intoProduct
    , intoFirst, intoLast
    , intoAnd, intoOr
    , intoAll, intoAny
    , intoFind, intoFindIndex
    , intoMinimum, intoMaximum
    , intoMinimumBy, intoMaximumBy
    , intoMonoid, intoFoldMap
    , intoFold, intoFold1
    , intoFor_
    -- * Transducers
    , mapping
    , filtering
    , concatMapping
    , taking, takingWhile
    , dropping, droppingWhile
    , enumerating
    , prescanning, postscanning
    ) where

import Control.Applicative (liftA2)
import Data.Maybe (fromMaybe)
import Prelude hiding (init, pred)

-- types

data Reduced a = Reduced { _flag :: !Bool, getReduced :: a }

continue :: a -> Reduced a
continue = Reduced False

reduced :: a -> Reduced a
reduced = Reduced True

instance Functor Reduced where
    fmap f (Reduced flag x) = Reduced flag (f x)

data Reducer a b = forall s. Reducer
    { _init :: s
    , _step :: s -> a -> Reduced s
    , _complete :: s -> b
    }

-- TODO: rename?

reducer :: s -> (s -> a -> Reduced s) -> (s -> b) -> Reducer a b
reducer = Reducer

reducer_ :: s -> (s -> a -> s) -> (s -> b) -> Reducer a b
reducer_ init step = Reducer init (\acc x -> continue (step acc x))

type Transducer a b = forall r. Reducer b r -> Reducer a r

instance Functor (Reducer a) where
    fmap f (Reducer init step complete) = Reducer init step (f . complete)

instance Applicative (Reducer a) where
    pure x = Reducer () (\() _ -> reduced ()) (\() -> x)

    liftA2 f (Reducer initL stepL completeL) (Reducer initR stepR completeR) = Reducer init step complete
      where
        init = (continue initL, continue initR)
        step (l@(Reduced flagL xL), r@(Reduced flagR xR)) x
            | flagL =
                let r'@(Reduced flagR' _) = stepR xR x
                in Reduced flagR' (l, r')
            | flagR =
                let l'@(Reduced flagL' _) = stepL xL x
                in Reduced flagL' (l', r)
            | otherwise =
                let l'@(Reduced flagL' _) = stepL xL x
                    r'@(Reduced flagR' _) = stepR xR x
                in Reduced (flagL' && flagR') (l', r')
        complete (l, r) = f (completeL (getReduced l)) (completeR (getReduced r))

-- consumers

reduce :: (Foldable t) => Reducer a b -> t a -> b
reduce (Reducer init step complete) xs = foldr c complete xs init
  where
    c x k acc =
        let Reduced flag x' = step acc x
        in if flag then complete x' else k $! x'

transduce :: (Foldable t) => Transducer a b -> Reducer b c -> t a -> c
transduce trans red = reduce (trans red)

-- reducers

intoLength :: Reducer a Int
intoLength = intoFold (\x _ -> x + 1) 0

intoNull :: Reducer a Bool
intoNull = Reducer True (\_ _ -> reduced False) id

intoElem :: (Eq a) => a -> Reducer a Bool
intoElem x = intoAny (== x)

intoList :: Reducer a [a]
intoList = reducer_ id (\acc x -> acc . (x :)) ($ [])

intoRevList :: Reducer a [a]
intoRevList = intoFold (flip (:)) []

intoSum :: (Num a) => Reducer a a
intoSum = intoFold (+) 0

intoProduct :: (Num a) => Reducer a a
intoProduct = intoFold (*) 1

intoFirst :: Reducer a (Maybe a)
intoFirst = Reducer Nothing (\_ x -> reduced (Just x)) id

intoLast :: Reducer a (Maybe a)
intoLast = intoFold (const Just) Nothing

intoAnd :: Reducer Bool Bool
intoAnd = Reducer True (\acc x -> if x then continue acc else reduced x) id

intoOr :: Reducer Bool Bool
intoOr = Reducer False (\acc x -> if x then reduced x else continue acc) id

intoAll :: (a -> Bool) -> Reducer a Bool
intoAll pred = mapping pred intoAnd

intoAny :: (a -> Bool) -> Reducer a Bool
intoAny pred = mapping pred intoOr

intoFind :: (a -> Bool) -> Reducer a (Maybe a)
intoFind pred = filtering pred intoFirst

intoFindIndex :: (a -> Bool) -> Reducer a (Maybe Int)
intoFindIndex pred = enumerating . filtering (\(_, x) -> pred x) . mapping fst $ intoFirst

intoMinimum :: (Ord a) => Reducer a (Maybe a)
intoMinimum = intoFold f Nothing
  where
    f Nothing y = Just y
    f (Just x) y = Just (min x y)

intoMaximum :: (Ord a) => Reducer a (Maybe a)
intoMaximum = intoFold f Nothing
  where
    f Nothing y = Just y
    f (Just x) y = Just (max x y)

intoMinimumBy :: (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMinimumBy cmp = intoFold f Nothing
  where
    f Nothing x = Just x
    f (Just x) y = Just $ case x `cmp` y of
        GT -> y
        _ -> x

intoMaximumBy :: (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMaximumBy cmp = intoFold f Nothing
  where
    f Nothing x = Just x
    f (Just x) y = Just $ case x `cmp` y of
        LT -> y
        _ -> x

intoMonoid :: (Monoid m) => Reducer m m
intoMonoid = intoFold (<>) mempty

intoFoldMap :: (Monoid m) => (a -> m) -> (m -> b) -> Reducer a b
intoFoldMap f = reducer_ mempty (\acc x -> acc <> f x)

intoFold :: (b -> a -> b) -> b -> Reducer a b
intoFold f z = reducer_ z f id

intoFold1 :: (a -> a -> a) -> Reducer a a
intoFold1 f = reducer_ Nothing step (fromMaybe (error "intoFold1: empty structure"))
  where
    step Nothing x = Just x
    step (Just acc) x = Just $! f acc x

intoFor_ :: (Applicative f) => (a -> f b) -> Reducer a (f ())
intoFor_ f = intoFold (\acc x -> acc <* f x) (pure ())

-- transducers

-- TODO: simplify transducers using state & possibly use a strict tuple

mapping :: (a -> b) -> Transducer a b
mapping f (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = step acc (f x)
{-# INLINE mapping #-}

filtering :: (a -> Bool) -> Transducer a a
filtering pred (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = if pred x then step acc x else continue acc
{-# INLINE filtering #-}

concatMapping :: (Foldable t) => (a -> t b) -> Transducer a b
concatMapping f (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = continue $ reduce (Reducer acc step id) (f x)
{-# INLINE concatMapping #-}

taking :: Int -> Transducer a a
taking n (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (n, init)
    step' (n', acc) x
        | n' <= 0 = reduced (n', acc)
        | otherwise =
            let Reduced flag r' = step acc x
            in Reduced flag (if flag then n' else n' - 1, r')
    complete' (_, acc) = complete acc
{-# INLINE taking #-}

takingWhile :: (a -> Bool) -> Transducer a a
takingWhile pred (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = if pred x then step acc x else reduced acc
{-# INLINE takingWhile #-}

dropping :: Int -> Transducer a a
dropping n (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (n, init)
    step' (n', acc) x
        | n' <= 0 = fmap ((,) n') (step acc x)
        | otherwise = continue (n' - 1, acc)
    complete' (_, acc) = complete acc
{-# INLINE dropping #-}

droppingWhile :: (a -> Bool) -> Transducer a a
droppingWhile pred (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (False, init)
    step' (False, acc) x
        | pred x = continue (False, acc)
    step' (_, acc) x = fmap ((,) True) (step acc x)
    complete' (_, acc) = complete acc
{-# INLINE droppingWhile #-}

enumerating :: Transducer a (Int, a)
enumerating (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (0, init)
    step' (n, acc) x = fmap ((,) (n + 1)) (step acc (n, x))
    complete' (_, acc) = complete acc
{-# INLINE enumerating #-}

postscanning :: Reducer a b -> Transducer a b
postscanning (Reducer init0 step0 complete0) (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (init0, init)
    step' (acc0, acc) x =
        let Reduced flag0 acc0' = step0 acc0 x
            Reduced flag acc' = step acc (complete0 acc0')
        in Reduced (flag0 || flag) (acc0', acc')
    complete' (_, acc) = complete acc
{-# INLINE postscanning #-}

prescanning :: Reducer a b -> Transducer a b
prescanning (Reducer init0 step0 complete0) (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (init0, init)
    step' (acc0, acc) x =
        let Reduced flag0 acc0' = step0 acc0 x
            Reduced flag acc' = step acc (complete0 acc0)
        in Reduced (flag0 || flag) (acc0', acc')
    complete' (_, acc) = complete acc
{-# INLINE prescanning #-}
