{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

-- | For a good explanation, see [here](https://hypirion.com/musings/haskell-transducers).

module Data.Transducer
    ( Reduced(Reduced), continue, reduced
    , Reducer(Reducer)
    , Transducer
    -- * Reducers
    , reduce
    , intoSum, intoList, intoFirst, intoLast
    -- * Transducers
    , transduce
    , mapping, filtering, concatMapping, taking, takingWhile, dropping, droppingWhile
    ) where

import Prelude hiding (init, pred)

-- types

data Reduced a = Reduced { flag :: !Bool, getReduced :: !a }

continue :: a -> Reduced a
continue = Reduced False
{-# INLINE continue #-}

reduced :: a -> Reduced a
reduced = Reduced True
{-# INLINE reduced #-}

instance Functor Reduced where
    fmap f (Reduced flag x) = Reduced flag (f x)

data Reducer a b = forall r. Reducer
    { _init :: r
    , _step :: r -> a -> Reduced r
    , _complete :: r -> b
    }

type Transducer a b = forall r. Reducer b r -> Reducer a r

-- reducers

reduce :: Foldable t => Reducer a b -> t a -> b
reduce (Reducer init step complete) xs = complete $ getReduced (foldr c continue xs init)
  where
    c x k r =
        let r'@(Reduced flag x') = step r x
        in if flag then r' else k $! x'
{-# INLINE reduce #-}

intoSum :: Num a => Reducer a a
intoSum = Reducer 0 step id
  where
    step r x = continue (r + x)

intoList :: Reducer a [a]
intoList = Reducer id (\x a -> continue (x . (a :))) ($ [])

intoFirst :: Reducer a (Maybe a)
intoFirst = Reducer Nothing step id
  where
    step _ x = reduced (Just x)

intoLast :: Reducer a (Maybe a)
intoLast = Reducer Nothing step id
  where
    step _ x = continue (Just x)

-- transducers

transduce :: Foldable t => Transducer a b -> Reducer b c -> t a -> c
transduce transducer reducer = reduce (transducer reducer)
{-# INLINE transduce #-}

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

concatMapping :: Foldable t => (a -> t b) -> Transducer a b
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
        | n' <= 0 = fmap (\r' -> (n', r')) (step r x)
        | otherwise = continue (n' - 1, r)
    complete' (_, r) = complete r
{-# INLINE dropping #-}

droppingWhile :: (a -> Bool) -> Transducer a a
droppingWhile pred (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (False, init)
    step' (False, r) x
        | pred x = continue (False, r)
    step' (_, r) x = fmap (\r' -> (True, r')) (step r x)
    complete' (_, r) = complete r
{-# INLINE droppingWhile #-}
