{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

{- |
Transducers are composable algorithmic transformations.

= See also

* https://clojure.org/reference/transducers
* https://hypirion.com/musings/haskell-transducers
-}

module Transducers
    ( Reduced(Reduced), continue, reduced, getReduced
    , Reducer(..), reducer, reducer_
    , Transducer
    -- * Reducers
    , reduce
    , intoList, intoRevList
    , intoLength
    , intoNull
    , intoSum, intoProduct
    , intoFirst, intoLast
    , intoAnd, intoOr
    , intoAll, intoAny
    , intoMinimum, intoMaximum
    , intoMinimumBy, intoMaximumBy
    -- * Transducers
    , transduce
    , mapping
    , filtering
    , concatMapping
    , taking, takingWhile
    , dropping, droppingWhile
    , prescanning, postscanning
    ) where

import Control.Applicative (liftA2)
import Prelude hiding (init, pred)

-- TODO: indexing related stuff (elemIndex, enumerating, ...)?
-- TODO: elem, find, index?

-- types

data Reduced a = Reduced { _flag :: !Bool, getReduced :: !a }

-- TODO: different name?
continue :: a -> Reduced a
continue = Reduced False

reduced :: a -> Reduced a
reduced = Reduced True

-- FIXME: unlawful instance? :(
instance Functor Reduced where
    fmap f (Reduced flag x) = Reduced flag (f x)

data Reducer a b = forall r. Reducer
    { _init :: r
    , _step :: r -> a -> Reduced r
    , _complete :: r -> b
    }

-- TODO: rename?
-- TODO: variant where _complete is id?

reducer :: r -> (r -> a -> Reduced r) -> (r -> b) -> Reducer a b
reducer = Reducer

reducer_ :: r -> (r -> a -> r) -> (r -> b) -> Reducer a b
reducer_ init step complete = Reducer init (\r x -> continue (step r x)) complete

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

-- reducers

reduce :: (Foldable t) => Reducer a b -> t a -> b
reduce (Reducer init step complete) xs = foldr c complete xs init
  where
    c x k r =
        let Reduced flag x' = step r x
        in if flag then complete x' else k $! x'

intoLength :: Reducer a Int
intoLength = reducer_ 0 (\x _ -> x + 1) id

intoNull :: Reducer a Bool
intoNull = Reducer True (\_ _ -> reduced False) id

intoList :: Reducer a [a]
intoList = reducer_ id (\x a -> x . (a :)) ($ [])

intoRevList :: Reducer a [a]
intoRevList = reducer_ [] (flip (:)) id

intoSum :: (Num a) => Reducer a a
intoSum = reducer_ 0 (+) id

intoProduct :: (Num a) => Reducer a a
intoProduct = reducer_ 1 (*) id

intoFirst :: Reducer a (Maybe a)
intoFirst = Reducer Nothing (\_ x -> reduced (Just x)) id

intoLast :: Reducer a (Maybe a)
intoLast = reducer_ Nothing (const Just) id

intoAnd :: Reducer Bool Bool
intoAnd = Reducer True (\r x -> if x then continue r else reduced x) id

intoOr :: Reducer Bool Bool
intoOr = Reducer False (\r x -> if x then reduced x else continue r) id

intoAll :: (a -> Bool) -> Reducer a Bool
intoAll pred = mapping pred intoAnd

intoAny :: (a -> Bool) -> Reducer a Bool
intoAny pred = mapping pred intoOr

intoMinimum :: (Ord a) => Reducer a (Maybe a)
intoMinimum = reducer_ Nothing step id
  where
    step Nothing y = Just y
    step (Just x) y = Just (min x y)

intoMaximum :: (Ord a) => Reducer a (Maybe a)
intoMaximum = reducer_ Nothing step id
  where
    step Nothing y = Just y
    step (Just x) y = Just (max x y)

intoMinimumBy :: (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMinimumBy cmp = reducer_ Nothing step id
  where
    step Nothing x = Just x
    step (Just x) y = Just $ case x `cmp` y of
        GT -> y
        _ -> x

intoMaximumBy :: (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMaximumBy cmp = reducer_ Nothing step id
  where
    step Nothing x = Just x
    step (Just x) y = Just $ case x `cmp` y of
        LT -> y
        _ -> x

-- transducers

-- TODO: simplify transducers using state & possibly use a strict tuple

transduce :: (Foldable t) => Transducer a b -> Reducer b c -> t a -> c
transduce transducer reducer = reduce (transducer reducer)

mapping :: (a -> b) -> Transducer a b
mapping f (Reducer init step complete) = Reducer init step' complete
  where
    step' r x = step r (f x)
{-# INLINE mapping #-}

filtering :: (a -> Bool) -> Transducer a a
filtering pred (Reducer init step complete) = Reducer init step' complete
  where
    step' r x = if pred x then step r x else continue r
{-# INLINE filtering #-}

concatMapping :: (Foldable t) => (a -> t b) -> Transducer a b
concatMapping f (Reducer init step complete) = Reducer init step' complete
  where
    step' r x = continue $ reduce (Reducer r step id) (f x)
{-# INLINE concatMapping #-}

taking :: Int -> Transducer a a
taking n (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (n, init)
    step' (n', r) x
        | n' <= 0 = reduced (n', r)
        | otherwise =
            let Reduced flag r' = step r x
            in Reduced flag (if flag then n' else n' - 1, r')
    complete' (_, r) = complete r
{-# INLINE taking #-}

takingWhile :: (a -> Bool) -> Transducer a a
takingWhile pred (Reducer init step complete) = Reducer init step' complete
  where
    step' r x = if pred x then step r x else reduced r
{-# INLINE takingWhile #-}

dropping :: Int -> Transducer a a
dropping n (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (n, init)
    step' (n', r) x
        | n' <= 0 = fmap ((,) n') (step r x)
        | otherwise = continue (n' - 1, r)
    complete' (_, r) = complete r
{-# INLINE dropping #-}

droppingWhile :: (a -> Bool) -> Transducer a a
droppingWhile pred (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (False, init)
    step' (False, r) x
        | pred x = continue (False, r)
    step' (_, r) x = fmap ((,) True) (step r x)
    complete' (_, r) = complete r
{-# INLINE droppingWhile #-}

postscanning :: Reducer a b -> Transducer a b
postscanning (Reducer init0 step0 complete0) (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (init0, init)
    step' (r0, r) x =
        let Reduced flag0 r0' = step0 r0 x
            Reduced flag r' = step r (complete0 r0')
        in Reduced (flag0 || flag) (r0', r')
    complete' (_, r) = complete r
{-# INLINE postscanning #-}

prescanning :: Reducer a b -> Transducer a b
prescanning (Reducer init0 step0 complete0) (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (init0, init)
    step' (r0, r) x =
        let Reduced flag0 r0' = step0 r0 x
            Reduced flag r' = step r (complete0 r0)
        in Reduced (flag0 || flag) (r0', r')
    complete' (_, r) = complete r
{-# INLINE prescanning #-}
