{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

-- | For a good explanation, see [here](https://hypirion.com/musings/haskell-transducers).

module Transducers
    ( Reduced(Reduced), continue, reduced, getReduced
    , Reducer(Reducer), reducer'
    , Transducer
    -- * Reducers
    , reduce
    , intoList, intoRevList
    , intoLength
    , intoNull
    , intoSum, intoProduct
    , intoFirst, intoLast
    , intoAnd, intoOr
    , intoMin, intoMax
    -- * Transducers
    , transduce
    , mapping
    , filtering
    , concatMapping
    , taking, takingWhile
    , dropping, droppingWhile
    , prescanning, postscanning
    ) where

import Prelude hiding (init, pred)

-- types

data Reduced a = Reduced { _flag :: !Bool, getReduced :: !a }

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

reducer' :: r -> (r -> a -> r) -> (r -> b) -> Reducer a b
reducer' init step complete = Reducer init step' complete
  where
    step' r x = continue (step r x)
{-# INLINE reducer' #-}

type Transducer a b = forall r. Reducer b r -> Reducer a r

instance Functor (Reducer a) where
    fmap f (Reducer init step complete) = Reducer init step complete'
      where
        complete' x = f $! complete x

instance Applicative (Reducer a) where
    pure x = Reducer () (\() _ -> reduced ()) (\() -> x)

    Reducer initL stepL completeL <*> Reducer initR stepR completeR = Reducer init step complete
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
        complete (l, r) = completeL (getReduced l) $ completeR (getReduced r)
    {-# INLINE (<*>) #-}

-- reducers

reduce :: (Foldable t) => Reducer a b -> t a -> b
reduce (Reducer init step complete) xs = complete $ getReduced (foldr c continue xs init)
  where
    c x k r =
        let r'@(Reduced flag x') = step r x
        in if flag then r' else k $! x'
{-# INLINE reduce #-}

intoLength :: Reducer a Int
intoLength = reducer' 0 (\x _ -> x + 1) id

intoNull :: Reducer a Bool
intoNull = Reducer True (\_ _ -> reduced False) id

intoList :: Reducer a [a]
intoList = reducer' id (\x a -> x . (a :)) ($ [])

intoRevList :: Reducer a [a]
intoRevList = reducer' [] (flip (:)) id

intoSum :: (Num a) => Reducer a a
intoSum = reducer' 0 (+) id

intoProduct :: (Num a) => Reducer a a
intoProduct = reducer' 1 (*) id

intoFirst :: Reducer a (Maybe a)
intoFirst = Reducer Nothing step id
  where
    step _ x = reduced (Just x)

intoLast :: Reducer a (Maybe a)
intoLast = reducer' Nothing (const Just) id

intoAnd :: Reducer Bool Bool
intoAnd = reducer' True (&&) id

intoOr :: Reducer Bool Bool
intoOr = reducer' False (||) id

intoMin :: (Ord a) => Reducer a (Maybe a)
intoMin = reducer' Nothing step id
  where
    step Nothing x = Just x
    step (Just x) y = Just (min x y)

intoMax :: (Ord a) => Reducer a (Maybe a)
intoMax = reducer' Nothing step id
  where
    step Nothing x = Just x
    step (Just x) y = Just (max x y)

-- transducers

transduce :: (Foldable t) => Transducer a b -> Reducer b c -> t a -> c
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
