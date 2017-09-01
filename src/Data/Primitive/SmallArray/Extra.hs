{-# language BangPatterns #-}
{-# language RankNTypes #-}
{-# options_ghc -Wno-orphans #-}

module Data.Primitive.SmallArray.Extra
    ( newSmallArray_
    , strictMapSmallArray
    , deleteSmallArray
    , insertSmallArray
    , insertSmallArrayM
    , runSmallArray
    , unsafeUpdateSmallArrayM
    , updateSmallArray
    , updateSmallArrayM
    , updateSmallArrayWith'
    , fromList
    ) where

import Control.DeepSeq
import qualified GHC.Exts
import Control.Monad.ST (ST, runST)
import qualified Data.Foldable as F
import Data.Primitive.SmallArray

newSmallArray_ :: Int -> ST s (SmallMutableArray s a)
newSmallArray_ n = newSmallArray n (error "undefined smallarray element")
{-# inline newSmallArray_ #-}

strictMapSmallArray :: (a -> b) -> SmallArray a -> SmallArray b
strictMapSmallArray f = \ ary ->
    let !n = F.length ary
    in runSmallArray $ do
        mary <- newSmallArray_ n
        go ary mary 0 n
  where
    go ary mary i n
        | i >= n    = return mary
        | otherwise = do
             writeSmallArray mary i $! f (indexSmallArray ary i)
             go ary mary (i+1) n
{-# inline strictMapSmallArray #-}

runSmallArray :: (forall s . ST s (SmallMutableArray s e)) -> SmallArray e
runSmallArray act = runST $ act >>= unsafeFreezeSmallArray
{-# inline runSmallArray #-}

deleteSmallArray :: SmallArray e -> Int -> SmallArray e
deleteSmallArray ary idx = runST (deleteSmallArrayM ary idx)
{-# inline deleteSmallArray #-}

-- | /O(n)/ Delete an element at the given position in this array,
-- decreasing its size by one.
deleteSmallArrayM :: SmallArray e -> Int -> ST s (SmallArray e)
deleteSmallArrayM ary idx = do
    mary <- newSmallArray_ (count-1)
    copySmallArray mary 0 ary 0 idx
    copySmallArray mary idx ary (idx+1) (count-(idx+1))
    unsafeFreezeSmallArray mary
  where !count = length ary
{-# inline deleteSmallArrayM #-}

-- | /O(n)/ Insert an element at the given position in this array,
-- increasing its size by one.
insertSmallArray :: SmallArray e -> Int -> e -> SmallArray e
insertSmallArray ary idx b = runST (insertSmallArrayM ary idx b)
{-# inline insertSmallArray #-}

-- | /O(n)/ Insert an element at the given position in this array,
-- increasing its size by one.
insertSmallArrayM :: SmallArray e -> Int -> e -> ST s (SmallArray e)
insertSmallArrayM ary idx b = do
    mary <- newSmallArray_ (count + 1)
    copySmallArray mary 0 ary 0 idx
    writeSmallArray mary idx b
    copySmallArray mary (idx+1) ary idx (count-idx)
    unsafeFreezeSmallArray mary
  where !count = length ary
{-# inline insertSmallArrayM #-}

-- | /O(n)/ Update the element at the given position in this array.
updateSmallArray :: SmallArray e -> Int -> e -> SmallArray e
updateSmallArray ary idx b = runST (updateSmallArrayM ary idx b)
{-# inline updateSmallArray #-}

-- | /O(n)/ Update the element at the given position in this array.
updateSmallArrayM :: SmallArray e -> Int -> e -> ST s (SmallArray e)
updateSmallArrayM ary idx b = do
    mary <- thawSmallArray ary 0 count
    writeSmallArray mary idx b
    unsafeFreezeSmallArray mary
  where !count = length ary
{-# inline updateSmallArrayM #-}

-- | /O(n)/ Update the element at the given positio in this array, by
-- applying a function to it.  Evaluates the element to WHNF before
-- inserting it into the array.
updateSmallArrayWith' :: SmallArray e -> Int -> (e -> e) -> SmallArray e
updateSmallArrayWith' ary idx f = updateSmallArray ary idx $! f (indexSmallArray ary idx)
{-# inline updateSmallArrayWith' #-}

-- | /O(1)/ Update the element at the given position in this array,
-- without copying.
unsafeUpdateSmallArrayM :: SmallArray e -> Int -> e -> ST s ()
unsafeUpdateSmallArrayM ary idx b = do
    mary <- unsafeThawSmallArray ary
    writeSmallArray mary idx b
    _ <- unsafeFreezeSmallArray mary
    return ()
{-# inline unsafeUpdateSmallArrayM #-}

instance NFData a => NFData (SmallArray a) where
  rnf a0 = go a0 (length a0) 0 where
    go !a !n !i
      | i >= n = ()
      | otherwise = rnf (indexSmallArray a i) `seq` go a n (i + 1)
  {-# inline rnf #-} 

fromList :: [a] -> SmallArray a
fromList = GHC.Exts.fromList