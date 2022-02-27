{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

{- |
Transducers are composable algorithmic transformations.

A @'Reducer' a b@ is a description of a strict left fold over elements of type @a@ with
a completion transformation that produces a value of type @b@ and the possibility
to early exit (through 'Reduced').

A @'Transducer' a b@ is a function @forall r. Reducer b r -> Reducer a r@. Note that transducer composition is backwards,
so @f . g@ first applies @f@ and then @g@.

= Usage

There are no name clashes with the "Prelude", so this module can be imported unqualified:

> import Transducers

== Example

>>> transduce (filtering odd . mapping (+ 1)) intoSum [1..5]
12

The 'Applicative' instance of @'Reducer' a@ can be used to combine reducers.
The combined reducer will traverse the input only once.

>>> intoAverage = (/) <$> intoSum <*> fmap fromIntegral intoLength
>>> reduce intoAverage [1..10]
5.5

== Defining reucers/transducers

Reducers can be defined by using 'Reducer', 'mkReducer_' or one of the predefined combinators.
Additionally, applying a transducer to a reducer produces a new reducer. For example:

> intoSum = intoFold (+) 0
> intoAny pred = mapping pred intoOr

Transducers can be defined by using one of the combinators, by manually writing a function
`Reducer b r -> Reducer a r`, or by composing existing transducers. For example:

> mapping f (Reducer init step complete) = Reducer init (\acc x -> step acc (f x)) complete
> slicing i len = dropping i . taking len

It is recommended to mark transducers with the
[@INLINE@ pragma](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/exts/pragmas.html#pragma-INLINE)
for performance.

= Naming convention

Reducers are prefixed with "into" (e.g. 'intoSum'), while transducers have an "ing" suffix (e.g. 'mapping').

= See also

* https://clojure.org/reference/transducers
* https://hypirion.com/musings/haskell-transducers
-}

module Transducers
    ( Reduced(Reduced), continue, reduced, getReduced
    , Reducer(..), mkReducer_
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
import Prelude hiding (init, pred)

-- types

-- | A type to indicate wether or not the result of a reduction is already fully reduced.
data Reduced a = Reduced !Bool a -- Note: Using a 'Bool' flag is more efficient than @data Reduced a = Continue a | Reduced a@

-- | Extract the inner value.
getReduced :: Reduced a -> a
getReduced (Reduced _ x) = x

-- | A 'Reduced' that indicated to continue the reduction.
continue :: a -> Reduced a
continue = Reduced False

-- | A 'Reduced' that indicates to early exit the reduction.
reduced :: a -> Reduced a
reduced = Reduced True

instance Functor Reduced where
    fmap f (Reduced flag x) = Reduced flag (f x)

-- | A description of a reduction (strict left fold).
data Reducer a b = forall s. Reducer
    s -- ^ The initial state.
    (s -> a -> Reduced s) -- ^ The step function.
    (s -> b) -- ^ The completion function.

-- | Make a 'Reducer' from an initial state, a step function and a completion function.
-- The result of the step function is wrapped with 'continue'.
mkReducer_ :: s -> (s -> a -> s) -> (s -> b) -> Reducer a b
mkReducer_ init step = Reducer init (\acc x -> continue (step acc x))

-- | A transducer is a transformation from reducers to reducers.
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

-- | Reduce a 'Foldable' with a reducer.
reduce :: (Foldable t) => Reducer a b -> t a -> b
reduce (Reducer init step complete) xs = foldr c complete xs init
  where
    c x k acc =
        let Reduced flag x' = step acc x
        in if flag then complete x' else k $! x'

-- | Reduce a 'Foldable' with a reducer, after applying the transducer.
--
-- > transducer transducer reducer = reduce (transducer reducer)
transduce :: (Foldable t) => Transducer a b -> Reducer b c -> t a -> c
transduce transducer reducer = reduce (transducer reducer)

-- reducers

-- | Returns the number of elements.
intoLength :: Reducer a Int
intoLength = intoFold (\x _ -> x + 1) 0

-- | Returns 'True' if there are no elements, `False` otherwise.
intoNull :: Reducer a Bool
intoNull = Reducer True (\_ _ -> reduced False) id

-- | @intoElem x@ returns 'True' if @x@ is equal to any of the elements.
intoElem :: (Eq a) => a -> Reducer a Bool
intoElem x = intoAny (== x)

-- | Returns a list of all elements.
intoList :: Reducer a [a]
intoList = mkReducer_ id (\acc x -> acc . (x :)) ($ [])

-- | Returns a list of all elements, in reverse order.
intoRevList :: Reducer a [a]
intoRevList = intoFold (flip (:)) []

-- | Returns the sum of all elements.
intoSum :: (Num a) => Reducer a a
intoSum = intoFold (+) 0

-- | Returns the product of all elements.
intoProduct :: (Num a) => Reducer a a
intoProduct = intoFold (*) 1

-- | Returns the first element or 'Nothing' if there are no elements.
intoFirst :: Reducer a (Maybe a)
intoFirst = Reducer Nothing (\_ x -> reduced (Just x)) id

-- | Returns the last element or 'Nothing' if there are no elements.
intoLast :: Reducer a (Maybe a)
intoLast = intoFold (const Just) Nothing

-- | Returns 'True' if all elements are 'True', 'False' otherwise.
intoAnd :: Reducer Bool Bool
intoAnd = Reducer True (\acc x -> if x then continue acc else reduced x) id

-- | Returns 'True' if any element is 'True', 'False' otherwise.
intoOr :: Reducer Bool Bool
intoOr = Reducer False (\acc x -> if x then reduced x else continue acc) id

-- | Returns 'True' if all elements satisfy the predicate, 'False' otherwise.
intoAll :: (a -> Bool) -> Reducer a Bool
intoAll pred = mapping pred intoAnd

-- | Returns 'True' if any element satisfies the predicate, 'False' otherwise.
intoAny :: (a -> Bool) -> Reducer a Bool
intoAny pred = mapping pred intoOr

-- | Returns the first element satisfying the predicate or 'Nothing' if no element satisfies the predicate.
intoFind :: (a -> Bool) -> Reducer a (Maybe a)
intoFind pred = filtering pred intoFirst

-- | Returns the index of the first element satisfying the predicate or 'Nothing' if no element satisfies the predicate.
intoFindIndex :: (a -> Bool) -> Reducer a (Maybe Int)
intoFindIndex pred = enumerating . filtering (\(_, x) -> pred x) . mapping fst $ intoFirst

-- | Returns the minimum element or 'Nothing' if there are no elements.
intoMinimum :: (Ord a) => Reducer a (Maybe a)
intoMinimum = intoFold step Nothing
  where
    step Nothing y = Just y
    step (Just x) y = Just $! min x y

-- | Returns the maximum element or 'Nothing' if there are no elements.
intoMaximum :: (Ord a) => Reducer a (Maybe a)
intoMaximum = intoFold step Nothing
  where
    step Nothing y = Just y
    step (Just x) y = Just $! max x y

-- | Returns the minimum element with respect to the given comparison function or 'Nothing' if there are no elements.
intoMinimumBy :: (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMinimumBy cmp = intoFold step Nothing
  where
    step Nothing x = Just x
    step (Just x) y = Just $! case x `cmp` y of
        GT -> y
        _ -> x

-- | Returns the maximum element with respect to the given comparison function or 'Nothing' if there are no elements.
intoMaximumBy :: (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMaximumBy cmp = intoFold step Nothing
  where
    step Nothing x = Just x
    step (Just x) y = Just $! case x `cmp` y of
        LT -> y
        _ -> x

-- | Reduces the elements with '<>'. Returns 'mempty' if there are no elements.
intoMonoid :: (Monoid m) => Reducer m m
intoMonoid = intoFold (<>) mempty

-- | Map each element to a monoid and reduce them (like 'intoMonoid'). In the end, the extraction function is applied.
--
-- >>> import Data.Monoid (Sum(..))
-- >>> reduce (intoFoldMap Sum getSum) [1, 2, 3]
-- 6
intoFoldMap :: (Monoid m) => (a -> m) -> (m -> b) -> Reducer a b
intoFoldMap f = mkReducer_ mempty (\acc x -> acc <> f x)

-- | Creates a reducer using the fold function and start accumulator.
intoFold :: (b -> a -> b) -> b -> Reducer a b
intoFold f z = mkReducer_ z f id

-- | Like 'intoFold', but uses the first element as start accumulator. If there are no elements, 'Nothing' is returned.
intoFold1 :: (a -> a -> a) -> Reducer a (Maybe a)
intoFold1 f = intoFold step Nothing
  where
    step Nothing x = Just x
    step (Just acc) x = Just $! f acc x

-- | Map each element to an 'Applicative' action and evaluate these actions (from left to right), ignoring the results.
intoFor_ :: (Applicative f) => (a -> f b) -> Reducer a (f ())
intoFor_ f = intoFold (\acc x -> acc <* f x) (pure ())

-- transducers

-- | Apply the function to every element.
mapping :: (a -> b) -> Transducer a b
mapping f (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = step acc (f x)
{-# INLINE mapping #-}

-- | Only keep the elements that satisfy the predicate.
filtering :: (a -> Bool) -> Transducer a a
filtering pred (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = if pred x then step acc x else continue acc
{-# INLINE filtering #-}

-- | Apply the function to every element and flatten the result.
concatMapping :: (Foldable t) => (a -> t b) -> Transducer a b
concatMapping f (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = continue $ reduce (Reducer acc step id) (f x)
{-# INLINE concatMapping #-}

-- | Take the first @n@ elements.
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

-- | Take elements while the predicate is satisifed.
takingWhile :: (a -> Bool) -> Transducer a a
takingWhile pred (Reducer init step complete) = Reducer init step' complete
  where
    step' acc x = if pred x then step acc x else reduced acc
{-# INLINE takingWhile #-}

-- | Drop the first @n@ elements.
dropping :: Int -> Transducer a a
dropping n (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (n, init)
    step' (n', acc) x
        | n' <= 0 = fmap ((,) n') (step acc x)
        | otherwise = continue (n' - 1, acc)
    complete' (_, acc) = complete acc
{-# INLINE dropping #-}

-- | Drop elements while the predicate is satisified.
droppingWhile :: (a -> Bool) -> Transducer a a
droppingWhile pred (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (False, init)
    step' (False, acc) x
        | pred x = continue (False, acc)
    step' (_, acc) x = fmap ((,) True) (step acc x)
    complete' (_, acc) = complete acc
{-# INLINE droppingWhile #-}

-- | Associate each element with its index.
enumerating :: Transducer a (Int, a)
enumerating (Reducer init step complete) = Reducer init' step' complete'
  where
    init' = (0, init)
    step' (n, acc) x = fmap ((,) (n + 1)) (step acc (n, x))
    complete' (_, acc) = complete acc
{-# INLINE enumerating #-}

-- | Yield the current result after each reducer step.
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

-- | Yield the current result before each reducer step.
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
