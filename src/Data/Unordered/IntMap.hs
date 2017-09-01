{-# language BangPatterns, DeriveDataTypeable, MagicHash #-}
{-# language ScopedTypeVariables #-}
{-# language PatternGuards #-}
{-# language RoleAnnotations #-}
{-# language TypeFamilies #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
{-# options_ghc -fno-full-laziness #-}

module Data.Unordered.IntMap
    (
      UnorderedIntMap(..)
    , Leaf(..)

      -- * Construction
    , empty
    , singleton

      -- * Basic interface
    , null
    , size
    , member
    , lookup
    , lookupDefault
    , (!)
    , insert
    , insertWith
    , unsafeInsert
    , delete
    , adjust
    , update
    , alter

      -- * Combine
      -- ** Union
    , union
    , unionWith
    , unionWithKey
    , unions

      -- * Transformations
    , map
    , mapWithKey
    , traverseWithKey

      -- * Difference and intersection
    , difference
    , differenceWith
    , intersection
    , intersectionWith
    , intersectionWithKey

      -- * Folds
    , foldl'
    , foldlWithKey'
    , foldr
    , foldrWithKey

      -- * Filter
    , mapMaybe
    , mapMaybeWithKey
    , filter
    , filterWithKey

      -- * Conversions
    , keys
    , elems

      -- ** Lists
    , toList
    , fromList
    , fromListWith

      -- Internals used by the strict version
    , Bitmap
    , bitmapIndexedOrFull
    , mask
    , index
    , bitsPerSubkey
    , fullNodeMask
    , sparseIndex
    , two
    , unionArrayBy
    , update16
    , update16M
    , update16With'
    , updateOrConcatWith
    , updateOrConcatWithKey
    , filterMapAux
    , equalKeys
    ) where

import Data.Coerce
import Data.Semigroup (Semigroup((<>)))
import Control.DeepSeq (NFData(rnf))
import Control.Monad.ST (ST, runST)
import Data.Bits ((.&.), (.|.), complement, popCount)
import qualified Data.Foldable as F
import qualified Data.List as L
import GHC.Exts ((==#), build, reallyUnsafePtrEquality#, Word(W#), Int(I#), uncheckedShiftL#, uncheckedShiftRL#)
import Prelude hiding (filter, foldr, lookup, map, null, pred)
import Text.Read hiding (step)

import qualified Data.Primitive.SmallArray as A
import qualified Data.Primitive.SmallArray.Extra as A
import Data.Typeable (Typeable)

import GHC.Exts (isTrue#)
import qualified GHC.Exts as Exts

import Data.Functor.Classes

-- | A set of values.  A set cannot contain duplicate values.
------------------------------------------------------------------------

data Leaf v = L {-# UNPACK #-} !Int v
  deriving (Eq)

instance NFData v => NFData (Leaf v) where
    rnf (L _ v) = rnf v

-- Invariant: The length of the 1st argument to 'Full' is
-- 2^bitsPerSubkey

-- | A map from (possibly newtyped) Int keys to values.
-- A map cannot contain duplicate keys;
-- each key can map to at most one value.
data UnorderedIntMap v
    = Empty
    | BitmapIndexed  {-# UNPACK #-} !Bitmap {-# UNPACK #-} !(A.SmallArray (UnorderedIntMap v))
    | Leaf {-# UNPACK #-} !(Leaf v)
    | Full {-# UNPACK #-} !(A.SmallArray (UnorderedIntMap v))
      deriving (Typeable)

type role UnorderedIntMap representational

instance NFData v => NFData (UnorderedIntMap v) where
    rnf Empty                 = ()
    rnf (BitmapIndexed _ ary) = rnf ary
    rnf (Leaf l)              = rnf l
    rnf (Full ary)            = rnf ary

instance Functor UnorderedIntMap where
    fmap = map

instance F.Foldable UnorderedIntMap where
    foldr f = foldrWithKey (const f)

instance Semigroup (UnorderedIntMap v) where
  (<>) = union
  {-# inline (<>) #-}

instance Monoid (UnorderedIntMap v) where
  mempty = empty
  {-# inline mempty #-}
  mappend = (<>)
  {-# inline mappend #-}

type Bitmap = Word
type Shift  = Int

instance Show1 UnorderedIntMap where
    liftShowsPrec spv slv d m =
        let sp = liftShowsPrec2 showsPrec showList spv slv
            sl = liftShowList2 showsPrec showList spv slv
        in showsUnaryWith (liftShowsPrec sp sl) "fromList" d (toList m)

instance Read1 UnorderedIntMap where
    liftReadsPrec rp rl = readsData $
        readsUnaryWith (liftReadsPrec rp' rl') "fromList" fromList
      where
        rp' = liftReadsPrec rp rl
        rl' = liftReadList rp rl

instance Read e => Read (UnorderedIntMap e) where
    readPrec = parens $ prec 10 $ do
      Ident "fromList" <- lexP
      xs <- readPrec
      return (fromList xs)

    readListPrec = readListPrecDefault

instance Show v => Show (UnorderedIntMap v) where
    showsPrec d m = showParen (d > 10) $
      showString "fromList " . shows (toList m)

instance Traversable UnorderedIntMap where
    traverse f = traverseWithKey (\(_ :: Int) -> f)

instance Eq1 UnorderedIntMap where
    liftEq = equal (==)

instance (Eq v) => Eq (UnorderedIntMap v) where
    (==) = equal (==) (==)

equal :: (Int -> Int -> Bool) -> (v -> v' -> Bool)
      -> UnorderedIntMap v -> UnorderedIntMap v' -> Bool
equal eqk eqv t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    -- If the two trees are the same, then their lists of 'Leaf's read from left to right should be the same

    go (Leaf l1 : tl1) (Leaf l2 : tl2)
      | leafEq l1 l2
      = go tl1 tl2
    go [] [] = True
    go _  _  = False

    leafEq (L k v) (L k' v') = eqk k k' && eqv v v'

instance Ord1 UnorderedIntMap where
    liftCompare = cmp compare

-- | The order is total.
instance Ord v => Ord (UnorderedIntMap v) where
    compare = cmp compare compare

cmp :: (Int -> Int -> Ordering) -> (v -> v' -> Ordering)
    -> UnorderedIntMap v -> UnorderedIntMap v' -> Ordering
cmp cmpk cmpv t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf l1 : tl1) (Leaf l2 : tl2)
      = leafCompare l1 l2 `mappend`
        go tl1 tl2
    go [] [] = EQ
    go [] _  = LT
    go _  [] = GT
    go _ _ = error "cmp: Should never happend, toList' includes non Leaf"

    leafCompare (L k v) (L k' v') = cmpk k k' `mappend` cmpv v v'

-- Same as 'equal' but doesn't compare the values.
equalKeys :: (Int -> Int -> Bool) -> UnorderedIntMap v -> UnorderedIntMap v' -> Bool
equalKeys eq t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf l1 : tl1) (Leaf l2 : tl2)
      | leafEq l1 l2
      = go tl1 tl2
    go [] [] = True
    go _  _  = False

    leafEq (L k _) (L k' _) = eq k k'

  -- Helper to get 'Leaf's as a list.
toList' :: UnorderedIntMap v -> [UnorderedIntMap v] -> [UnorderedIntMap v]
toList' (BitmapIndexed _ ary) a = F.foldr toList' a ary
toList' (Full ary)            a = F.foldr toList' a ary
toList' l@(Leaf _)          a = l : a
toList' Empty                 a = a

-- Helper function to detect 'Leaf's
isLeaf :: UnorderedIntMap v -> Bool
isLeaf (Leaf _)      = True
isLeaf _               = False

------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct an empty map.
empty :: UnorderedIntMap v
empty = Empty

-- | /O(1)/ Construct a map with a single element.
singleton :: Coercible key Int => key -> v -> UnorderedIntMap v
singleton (coerce -> k :: Int) v = Leaf (L k v)

------------------------------------------------------------------------
-- * Basic interface

-- | /O(1)/ Return 'True' if this map is empty, 'False' otherwise.
null :: UnorderedIntMap v -> Bool
null Empty = True
null _   = False

-- | /O(n)/ Return the number of key-value mappings in this map.
size :: UnorderedIntMap v -> Int
size t = go t 0
  where
    go Empty                !n = n
    go (Leaf _)            n = n + 1
    go (BitmapIndexed _ ary) n = F.foldl' (flip go) n ary
    go (Full ary)            n = F.foldl' (flip go) n ary

-- | /O(log n)/ Return 'True' if the specified key is present in the
-- map, 'False' otherwise.
member :: Coercible key Int => key -> UnorderedIntMap a -> Bool
member k m = case lookup k m of
    Nothing -> False
    Just _  -> True
{-# INLINABLE member #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or 'Nothing' if this map contains no mapping for the key.
lookup :: Coercible key Int => key -> UnorderedIntMap v -> Maybe v
lookup (coerce -> k0 :: Int) m0 = go k0 0 m0
  where
    go !_ !_ Empty = Nothing
    go k _ (Leaf (L kx x))
        | k == kx = Just x  -- TODO: Split test in two
        | otherwise          = Nothing
    go k s (BitmapIndexed b v)
        | b .&. m == 0 = Nothing
        | otherwise    = go k (s+bitsPerSubkey) (A.indexSmallArray v (sparseIndex b m))
      where m = mask k s
    go k s (Full v) = go k (s+bitsPerSubkey) (A.indexSmallArray v (index k s))
{-# INLINABLE lookup #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or the default value if this map contains no mapping for the key.
lookupDefault :: Coercible key Int =>
    v          -- ^ Default value to return.
    -> key -> UnorderedIntMap v -> v
lookupDefault def (coerce -> k :: Int) t = case lookup k t of
    Just v -> v
    _      -> def
{-# INLINABLE lookupDefault #-}

-- | /O(log n)/ Return the value to which the specified key is mapped.
-- Calls 'error' if this map contains no mapping for the key.
(!) :: Coercible key Int => UnorderedIntMap v -> key -> v
(!) m (coerce -> k :: Int) = case lookup k m of
    Just v  -> v
    Nothing -> error "Data.UnorderedIntMap.(!): key not found"
{-# INLINABLE (!) #-}

infixl 9 !

-- | Create a 'BitmapIndexed' or 'Full' node.
bitmapIndexedOrFull :: Bitmap -> A.SmallArray (UnorderedIntMap v) -> UnorderedIntMap v
bitmapIndexedOrFull b ary
    | b == fullNodeMask = Full ary
    | otherwise         = BitmapIndexed b ary
{-# inline bitmapIndexedOrFull #-}

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
insert :: Coercible key Int => key -> v -> UnorderedIntMap v -> UnorderedIntMap v
insert (coerce -> k0 :: Int) v0 m0 = go k0 v0 0 m0
  where
    go !k x !_ Empty = Leaf (L k x)
    go k x s t@(Leaf (L ky y))
        | ky == k =
            if x `ptrEq` y
            then t
            else Leaf (L k x)
        | otherwise = runST (two s k x ky y)
    go k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insertSmallArray ary i $! Leaf (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st  = A.indexSmallArray ary i
                !st' = go k x (s+bitsPerSubkey) st
            in if st' `ptrEq` st
               then t
               else BitmapIndexed b (A.updateSmallArray ary i st')
      where m = mask k s
            i = sparseIndex b m
    go k x s t@(Full ary) =
        let !st  = A.indexSmallArray ary i
            !st' = go k x (s+bitsPerSubkey) st
        in if st' `ptrEq` st
            then t
            else Full (update16 ary i st')
      where i = index k s
{-# INLINABLE insert #-}

-- | In-place update version of insert
unsafeInsert :: Coercible key Int => key -> v -> UnorderedIntMap v -> UnorderedIntMap v
unsafeInsert (coerce -> k0 :: Int) v0 m0 = runST (go k0 v0 0 m0)
  where
    go !k x !_ Empty = return $! Leaf (L k x)
    go k x s t@(Leaf (L ky y))
        | ky == k =
            if x `ptrEq` y
            then return t
            else return $! Leaf (L k x)
        | otherwise = two s k x ky y
    go k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertSmallArrayM ary i $! Leaf (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexSmallArrayM ary i
            st' <- go k x (s+bitsPerSubkey) st
            A.unsafeUpdateSmallArrayM ary i st'
            return t
      where m = mask k s
            i = sparseIndex b m
    go k x s t@(Full ary) = do
        st <- A.indexSmallArrayM ary i
        st' <- go k x (s+bitsPerSubkey) st
        A.unsafeUpdateSmallArrayM ary i st'
        return t
      where i = index k s
{-# INLINABLE unsafeInsert #-}

-- | Create a map from two key-value pairs which hashes don't collide.
two :: Shift -> Int -> v -> Int -> v -> ST s (UnorderedIntMap v)
two = go
  where
    go s k1 v1 k2 v2
        | bp1 == bp2 = do
            st <- go (s+bitsPerSubkey) k1 v1 k2 v2
            let ary = pure st
            return $! BitmapIndexed bp1 ary
        | otherwise  = do
            mary <- A.newSmallArray 2 $ Leaf (L k1 v1)
            A.writeSmallArray mary idx2 $ Leaf (L k2 v2)
            ary <- A.unsafeFreezeSmallArray mary
            return $! BitmapIndexed (bp1 .|. bp2) ary
      where
        bp1  = mask k1 s
        bp2  = mask k2 s
        idx2 | index k1 s < index k2 s = 1
             | otherwise               = 0
{-# inline two #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
insertWith :: Coercible key Int => (v -> v -> v) -> key -> v -> UnorderedIntMap v
            -> UnorderedIntMap v
insertWith f (coerce -> k0 :: Int) v0 m0 = go k0 v0 0 m0
  where
    go !k x !_ Empty = Leaf (L k x)
    go k x s (Leaf (L ky y))
        | ky == k = Leaf (L k (f x y))
        | otherwise = runST (two s k x ky y)
    go k x s (BitmapIndexed b ary)
        | b .&. m == 0 =
            let ary' = A.insertSmallArray ary i $! Leaf (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let st   = A.indexSmallArray ary i
                st'  = go k x (s+bitsPerSubkey) st
                ary' = A.updateSmallArray ary i $! st'
            in BitmapIndexed b ary'
      where m = mask k s
            i = sparseIndex b m
    go k x s (Full ary) =
        let st   = A.indexSmallArray ary i
            st'  = go k x (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
      where i = index k s
{-# INLINABLE insertWith #-}

-- | In-place update version of insertWith
unsafeInsertWith :: forall key v . Coercible key Int =>
                 (v -> v -> v) -> key -> v -> UnorderedIntMap v
                 -> UnorderedIntMap v
unsafeInsertWith f (coerce -> k0 :: Int) v0 m0 = runST (go k0 v0 0 m0)
  where
    go :: Int -> v -> Shift -> UnorderedIntMap v -> ST s (UnorderedIntMap v)
    go !k x !_ Empty = return $! Leaf (L k x)
    go k x s (Leaf (L ky y))
        | ky == k = return $! Leaf (L k (f x y))
        | otherwise = two s k x ky y
    go k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertSmallArrayM ary i $! Leaf (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexSmallArrayM ary i
            st' <- go k x (s+bitsPerSubkey) st
            A.unsafeUpdateSmallArrayM ary i st'
            return t
      where m = mask k s
            i = sparseIndex b m
    go k x s t@(Full ary) = do
        st <- A.indexSmallArrayM ary i
        st' <- go k x (s+bitsPerSubkey) st
        A.unsafeUpdateSmallArrayM ary i st'
        return t
      where i = index k s
{-# INLINABLE unsafeInsertWith #-}

-- | /O(log n)/ Remove the mapping for the specified key from this map
-- if present.
delete :: Coercible key Int => key -> UnorderedIntMap v -> UnorderedIntMap v
delete (coerce -> k0 :: Int) m0 = go k0 0 m0
  where
    go !_ !_ Empty = Empty
    go k _ t@(Leaf (L ky _))
        | ky == k = Empty
        | otherwise          = t
    go k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise =
            let !st = A.indexSmallArray ary i
                !st' = go k (s+bitsPerSubkey) st
            in if st' `ptrEq` st
                then t
                else case st' of
                Empty | F.length ary == 1 -> Empty
                      | F.length ary == 2 ->
                          case (i, A.indexSmallArray ary 0, A.indexSmallArray ary 1) of
                          (0, _, l) | isLeaf l -> l
                          (1, l, _) | isLeaf l -> l
                          _                               -> bIndexed
                      | otherwise -> bIndexed
                    where
                      bIndexed = BitmapIndexed (b .&. complement m) (A.deleteSmallArray ary i)
                l | isLeaf l && F.length ary == 1 -> l
                _ -> BitmapIndexed b (A.updateSmallArray ary i st')
      where m = mask k s
            i = sparseIndex b m
    go k s t@(Full ary) =
        let !st   = A.indexSmallArray ary i
            !st' = go k (s+bitsPerSubkey) st
        in if st' `ptrEq` st
            then t
            else case st' of
            Empty ->
                let ary' = A.deleteSmallArray ary i
                    bm   = fullNodeMask .&. complement (1 `unsafeShiftL` i)
                in BitmapIndexed bm ary'
            _ -> Full (A.updateSmallArray ary i st')
      where i = index k s
{-# INLINABLE delete #-}

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: Coercible key Int => (v -> v) -> key -> UnorderedIntMap v -> UnorderedIntMap v
adjust f (coerce -> k0 :: Int) m0 = go k0 0 m0
  where
    go !_ !_ Empty = Empty
    go k _ t@(Leaf (L ky y))
        | ky == k = Leaf (L k (f y))
        | otherwise          = t
    go k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let st   = A.indexSmallArray ary i
                          st'  = go k (s+bitsPerSubkey) st
                          ary' = A.updateSmallArray ary i $! st'
                      in BitmapIndexed b ary'
      where m = mask k s
            i = sparseIndex b m
    go k s (Full ary) =
        let i    = index k s
            st   = A.indexSmallArray ary i
            st'  = go k (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
{-# INLINABLE adjust #-}

-- | /O(log n)/  The expression (@'update' f k map@) updates the value @x@ at @k@,
-- (if it is in the map). If (f k x) is @'Nothing', the element is deleted.
-- If it is (@'Just' y), the key k is bound to the new value y.
update :: Coercible key Int => (a -> Maybe a) -> key -> UnorderedIntMap a -> UnorderedIntMap a
update f = alter (>>= f)
{-# INLINABLE update #-}


-- | /O(log n)/  The expression (@'alter' f k map@) alters the value @x@ at @k@, or
-- absence thereof. @alter@ can be used to insert, delete, or update a value in a
-- map. In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: Coercible key Int => (Maybe v -> Maybe v) -> key -> UnorderedIntMap v -> UnorderedIntMap v
alter f (coerce -> k :: Int) m =
  case f (lookup k m) of
    Nothing -> delete k m
    Just v  -> insert k v m
{-# INLINABLE alter #-}

------------------------------------------------------------------------
-- * Combine

-- | /O(n+m)/ The union of two maps. If a key occurs in both maps, the
-- mapping from the first will be the mapping in the result.
union :: UnorderedIntMap v -> UnorderedIntMap v -> UnorderedIntMap v
union = unionWith const
{-# INLINABLE union #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWith :: forall v. (v -> v -> v) -> UnorderedIntMap v -> UnorderedIntMap v
          -> UnorderedIntMap v
unionWith f = unionWithKey (const f :: Int -> v -> v -> v)
{-# inline unionWith #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWithKey :: Coercible key Int => (key -> v -> v -> v) -> UnorderedIntMap v -> UnorderedIntMap v
          -> UnorderedIntMap v
unionWithKey f = go 0
  where
    -- empty vs. anything
    go !_ t1 Empty = t1
    go _ Empty t2 = t2
    -- leaf vs. leaf
    go s t1@(Leaf (L k1 v1)) t2@(Leaf (L k2 v2))
        | k1 == k2 = Leaf (L k1 (f (coerce k1) v1 v2))
        | otherwise = goDifferentHash s k1 k2 t1 t2
    -- branch vs. branch
    go s (BitmapIndexed b1 ary1) (BitmapIndexed b2 ary2) =
        let b'   = b1 .|. b2
            ary' = unionArrayBy (go (s+bitsPerSubkey)) b1 b2 ary1 ary2
        in bitmapIndexedOrFull b' ary'
    go s (BitmapIndexed b1 ary1) (Full ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) b1 fullNodeMask ary1 ary2
        in Full ary'
    go s (Full ary1) (BitmapIndexed b2 ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) fullNodeMask b2 ary1 ary2
        in Full ary'
    go s (Full ary1) (Full ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) fullNodeMask fullNodeMask
                   ary1 ary2
        in Full ary'
    -- leaf vs. branch
    go s (BitmapIndexed b1 ary1) t2
        | b1 .&. m2 == 0 = let ary' = A.insertSmallArray ary1 i t2
                               b'   = b1 .|. m2
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateSmallArrayWith' ary1 i $ \st1 ->
                                   go (s+bitsPerSubkey) st1 t2
                           in BitmapIndexed b1 ary'
        where
          h2 = leafHashCode t2
          m2 = mask h2 s
          i = sparseIndex b1 m2
    go s t1 (BitmapIndexed b2 ary2)
        | b2 .&. m1 == 0 = let ary' = A.insertSmallArray ary2 i $! t1
                               b'   = b2 .|. m1
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateSmallArrayWith' ary2 i $ \st2 ->
                                   go (s+bitsPerSubkey) t1 st2
                           in BitmapIndexed b2 ary'
      where
        h1 = leafHashCode t1
        m1 = mask h1 s
        i = sparseIndex b2 m1
    go s (Full ary1) t2 =
        let h2   = leafHashCode t2
            i    = index h2 s
            ary' = update16With' ary1 i $ \st1 -> go (s+bitsPerSubkey) st1 t2
        in Full ary'
    go s t1 (Full ary2) =
        let h1   = leafHashCode t1
            i    = index h1 s
            ary' = update16With' ary2 i $ \st2 -> go (s+bitsPerSubkey) t1 st2
        in Full ary'

    leafHashCode (Leaf (L k _)) = k
    leafHashCode _ = error "leafHashCode"

    goDifferentHash s h1 h2 t1 t2
        | m1 == m2  = BitmapIndexed m1 (pure $! go (s+bitsPerSubkey) t1 t2)
        | m1 <  m2  = BitmapIndexed (m1 .|. m2) (A.fromList [t1, t2])
        | otherwise = BitmapIndexed (m1 .|. m2) (A.fromList [t2, t1])
      where
        m1 = mask h1 s
        m2 = mask h2 s
{-# inline unionWithKey #-}

-- | Strict in the result of @f@.
unionArrayBy :: (a -> a -> a) -> Bitmap -> Bitmap -> A.SmallArray a -> A.SmallArray a
             -> A.SmallArray a
unionArrayBy f b1 b2 ary1 ary2 = A.runSmallArray $ do
    let b' = b1 .|. b2
    mary <- A.newSmallArray_ (popCount b')
    -- iterate over nonzero bits of b1 .|. b2
    -- it would be nice if we could shift m by more than 1 each time
    let ba = b1 .&. b2
        go !i !i1 !i2 !m
            | m > b'        = return ()
            | b' .&. m == 0 = go i i1 i2 (m `unsafeShiftL` 1)
            | ba .&. m /= 0 = do
                A.writeSmallArray mary i $! f (A.indexSmallArray ary1 i1) (A.indexSmallArray ary2 i2)
                go (i+1) (i1+1) (i2+1) (m `unsafeShiftL` 1)
            | b1 .&. m /= 0 = do
                A.writeSmallArray mary i =<< A.indexSmallArrayM ary1 i1
                go (i+1) (i1+1) (i2  ) (m `unsafeShiftL` 1)
            | otherwise     = do
                A.writeSmallArray mary i =<< A.indexSmallArrayM ary2 i2
                go (i+1) (i1  ) (i2+1) (m `unsafeShiftL` 1)
    go 0 0 0 (b' .&. negate b') -- XXX: b' must be non-zero
    return mary
    -- TODO: For the case where b1 .&. b2 == b1, i.e. when one is a
    -- subset of the other, we could use a slightly simpler algorithm,
    -- where we copy one array, and then update.
{-# inline unionArrayBy #-}

-- TODO: Figure out the time complexity of 'unions'.

-- | Construct a set containing all elements from a list of sets.
unions :: [UnorderedIntMap v] -> UnorderedIntMap v
unions = L.foldl' union empty
{-# inline unions #-}

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: Coercible key Int => (key -> v1 -> v2) -> UnorderedIntMap v1 -> UnorderedIntMap v2
mapWithKey f = go
  where
    go Empty = Empty
    go (Leaf (L k v)) = Leaf $ L k (f (coerce k) v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.strictMapSmallArray go ary
    go (Full ary) = Full $ A.strictMapSmallArray go ary
{-# inline mapWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value.
map :: forall v1 v2 . (v1 -> v2) -> UnorderedIntMap v1 -> UnorderedIntMap v2
map f = mapWithKey (const f :: Int -> v1 -> v2)
{-# inline map #-}

-- TODO: We should be able to use mutation to create the new
-- 'UnorderedIntMap'.

-- | /O(n)/ Transform this map by accumulating an Applicative result
-- from every value.
traverseWithKey :: (Coercible key Int, Applicative f) => (key -> v1 -> f v2) -> UnorderedIntMap v1
                -> f (UnorderedIntMap v2)
traverseWithKey f = go
  where
    go Empty                 = pure Empty
    go (Leaf (L k v))      = Leaf . L k <$> f (coerce k) v
    go (BitmapIndexed b ary) = BitmapIndexed b <$> traverse go ary
    go (Full ary)            = Full <$> traverse go ary
{-# inline traverseWithKey #-}

------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n*log m)/ Difference of two maps. Return elements of the first map
-- not existing in the second.
difference :: UnorderedIntMap v -> UnorderedIntMap w -> UnorderedIntMap v
difference a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 _       -> m
{-# INLINABLE difference #-}

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWith :: (v -> w -> Maybe v) -> UnorderedIntMap v -> UnorderedIntMap w -> UnorderedIntMap v
differenceWith f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 Just w  -> maybe m (\y -> insert k y m) (f v w)
{-# INLINABLE differenceWith #-}

-- | /O(n*log m)/ Intersection of two maps. Return elements of the first
-- map for keys existing in the second.
intersection :: UnorderedIntMap v -> UnorderedIntMap w -> UnorderedIntMap v
intersection a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just _ -> insert k v m
                 _      -> m
{-# INLINABLE intersection #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWith :: (v1 -> v2 -> v3) -> UnorderedIntMap v1
                 -> UnorderedIntMap v2 -> UnorderedIntMap v3
intersectionWith f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just w -> insert k (f v w) m
                 _      -> m
{-# INLINABLE intersectionWith #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWithKey :: Coercible key Int => (key -> v1 -> v2 -> v3)
                    -> UnorderedIntMap v1 -> UnorderedIntMap v2 -> UnorderedIntMap v3
intersectionWithKey f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just w -> insert k (f (coerce k) v w) m
                 _      -> m
{-# INLINABLE intersectionWithKey #-}

------------------------------------------------------------------------
-- * Folds

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldl' :: (a -> v -> a) -> a -> UnorderedIntMap v -> a
foldl' f = foldlWithKey' (\ z _ v -> f z v)
{-# inline foldl' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldlWithKey' :: (a -> Int -> v -> a) -> a -> UnorderedIntMap v -> a
foldlWithKey' f = go
  where
    go !z Empty                = z
    go z (Leaf (L k v))      = f z k v
    go z (BitmapIndexed _ ary) = F.foldl' go z ary
    go z (Full ary)            = F.foldl' go z ary
{-# inline foldlWithKey' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (v -> a -> a) -> a -> UnorderedIntMap v -> a
foldr f = foldrWithKey (const f)
{-# inline foldr #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldrWithKey :: (Int -> v -> a -> a) -> a -> UnorderedIntMap v -> a
foldrWithKey f = go
  where
    go z Empty                 = z
    go z (Leaf (L k v))      = f k v z
    go z (BitmapIndexed _ ary) = F.foldr (flip go) z ary
    go z (Full ary)            = F.foldr (flip go) z ary
{-# inline foldrWithKey #-}

------------------------------------------------------------------------
-- * Filter

-- | Create a new array of the @n@ first elements of @mary@.
trim :: A.SmallMutableArray s a -> Int -> ST s (A.SmallArray a)
trim mary n = do
    mary2 <- A.newSmallArray_ n
    A.copySmallMutableArray mary2 0 mary 0 n
    A.unsafeFreezeSmallArray mary2
{-# inline trim #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybeWithKey :: (Int -> v1 -> Maybe v2) -> UnorderedIntMap v1 -> UnorderedIntMap v2
mapMaybeWithKey f = filterMapAux onLeaf
  where onLeaf (Leaf (L k v)) | Just v' <- f k v = Just (Leaf (L k v'))
        onLeaf _ = Nothing
{-# inline mapMaybeWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybe :: (v1 -> Maybe v2) -> UnorderedIntMap v1 -> UnorderedIntMap v2
mapMaybe f = mapMaybeWithKey (const f)
{-# inline mapMaybe #-}

-- | /O(n)/ Filter this map by retaining only elements satisfying a
-- predicate.
filterWithKey :: forall v. (Int -> v -> Bool) -> UnorderedIntMap v -> UnorderedIntMap v
filterWithKey pred = filterMapAux onLeaf
  where onLeaf t@(Leaf (L k v)) | pred k v = Just t
        onLeaf _ = Nothing
{-# inline filterWithKey #-}


-- | Common implementation for 'filterWithKey' and 'mapMaybeWithKey',
--   allowing the former to former to reuse terms.
filterMapAux :: forall v1 v2
              . (UnorderedIntMap v1 -> Maybe (UnorderedIntMap v2))
             -> UnorderedIntMap v1
             -> UnorderedIntMap v2
filterMapAux onLeaf = go
  where
    go Empty = Empty
    go t@Leaf{}
        | Just t' <- onLeaf t = t'
        | otherwise = Empty
    go (BitmapIndexed b ary) = filterA ary b
    go (Full ary) = filterA ary fullNodeMask

    filterA ary0 b0 =
        let !n = F.length ary0
        in runST $ do
            mary <- A.newSmallArray_ n
            step ary0 mary b0 0 0 1 n
      where
        step :: A.SmallArray (UnorderedIntMap v1) -> A.SmallMutableArray s (UnorderedIntMap v2)
             -> Bitmap -> Int -> Int -> Bitmap -> Int
             -> ST s (UnorderedIntMap v2)
        step !ary !mary !b i !j !bi n
            | i >= n = case j of
                0 -> return Empty
                1 -> do
                    ch <- A.readSmallArray mary 0
                    case ch of
                      t | isLeaf t -> return t
                      _                       -> BitmapIndexed b <$> trim mary 1
                _ -> do
                    ary2 <- trim mary j
                    return $! if j == maxChildren
                              then Full ary2
                              else BitmapIndexed b ary2
            | bi .&. b == 0 = step ary mary b i j (bi `unsafeShiftL` 1) n
            | otherwise = case go (A.indexSmallArray ary i) of
                Empty -> step ary mary (b .&. complement bi) (i+1) j
                         (bi `unsafeShiftL` 1) n
                t     -> do A.writeSmallArray mary j t
                            step ary mary b (i+1) (j+1) (bi `unsafeShiftL` 1) n
{-# inline filterMapAux #-}

-- | /O(n)/ Filter this map by retaining only elements which values
-- satisfy a predicate.
filter :: (v -> Bool) -> UnorderedIntMap v -> UnorderedIntMap v
filter p = filterWithKey (\_ v -> p v)
{-# inline filter #-}

------------------------------------------------------------------------
-- * Conversions

-- TODO: Improve fusion rules by modelled them after the Prelude ones
-- on lists.

-- | /O(n)/ Return a list of this map's keys.  The list is produced
-- lazily.
keys :: UnorderedIntMap v -> [Int]
keys = L.map fst . toList
{-# inline keys #-}

-- | /O(n)/ Return a list of this map's values.  The list is produced
-- lazily.
elems :: forall v. UnorderedIntMap v -> [v]
elems = L.map snd . (toList :: UnorderedIntMap v -> [(Int, v)])
{-# inline elems #-}

------------------------------------------------------------------------
-- ** Lists

-- | /O(n)/ Return a list of this map's elements.  The list is
-- produced lazily. The order of its elements is unspecified.
toList :: UnorderedIntMap v -> [(Int, v)]
toList t = build (\ c z -> foldrWithKey (\k v a -> c (k, v) a) z t)
{-# inline toList #-}

-- | /O(n)/ Construct a map with the supplied mappings.  If the list
-- contains duplicate mappings, the later mappings take precedence.
fromList :: [(Int, v)] -> UnorderedIntMap v
fromList = L.foldl' (\ m (k, v) -> unsafeInsert k v m) empty
{-# INLINABLE fromList #-}

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
fromListWith :: Coercible key Int => (v -> v -> v) -> [(key, v)] -> UnorderedIntMap v
fromListWith f = L.foldl' (\ m (coerce -> k :: Int, v) -> unsafeInsertWith f k v m) empty
{-# inline fromListWith #-}

------------------------------------------------------------------------
-- Array operations

-- | /O(n)/ Lookup the value associated with the given key in this
-- array.  Returns 'Nothing' if the key wasn't found.
indexOf :: Int -> A.SmallArray (Leaf v) -> Maybe Int
indexOf k0 ary0 = go k0 ary0 0 (F.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = Nothing
        | otherwise = case A.indexSmallArray ary i of
            (L kx _)
                | k == kx   -> Just i
                | otherwise -> go k ary (i+1) n
{-# INLINABLE indexOf #-}

updateOrConcatWith :: forall v. (v -> v -> v) -> A.SmallArray (Leaf v) -> A.SmallArray (Leaf v) -> A.SmallArray (Leaf v)
updateOrConcatWith f = updateOrConcatWithKey (const f :: Int -> v -> v -> v)
{-# INLINABLE updateOrConcatWith #-}

updateOrConcatWithKey :: (Int -> v -> v -> v) -> A.SmallArray (Leaf v) -> A.SmallArray (Leaf v) -> A.SmallArray (Leaf v)
updateOrConcatWithKey f ary1 ary2 = A.runSmallArray $ do
    -- first: look up the position of each element of ary2 in ary1
    let indices = fmap (\(L k _) -> indexOf k ary1) ary2
    -- that tells us how large the overlap is:
    -- count number of Nothing constructors
    let nOnly2 = F.foldl' (\n -> maybe (n+1) (const n)) 0 indices
    let n1 = F.length ary1
    let n2 = F.length ary2
    -- copy over all elements from ary1
    mary <- A.newSmallArray_ (n1 + nOnly2)
    A.copySmallArray mary 0 ary1 0 n1
    -- append or update all elements from ary2
    let go !iEnd !i2
          | i2 >= n2 = return ()
          | otherwise = case A.indexSmallArray indices i2 of
               Just i1 -> do -- key occurs in both arrays, store combination in position i1
                             L k v1 <- A.indexSmallArrayM ary1 i1
                             L _ v2 <- A.indexSmallArrayM ary2 i2
                             A.writeSmallArray mary i1 (L k (f k v1 v2))
                             go iEnd (i2+1)
               Nothing -> do -- key is only in ary2, append to end
                             A.writeSmallArray mary iEnd =<< A.indexSmallArrayM ary2 i2
                             go (iEnd+1) (i2+1)
    go n1 0
    return mary
{-# INLINABLE updateOrConcatWithKey #-}

------------------------------------------------------------------------
-- Manually unrolled loops

-- | /O(n)/ Update the element at the given position in this array.
update16 :: A.SmallArray e -> Int -> e -> A.SmallArray e
update16 ary idx b = runST (update16M ary idx b)
{-# inline update16 #-}

-- | /O(n)/ Update the element at the given position in this array.
update16M :: A.SmallArray e -> Int -> e -> ST s (A.SmallArray e)
update16M ary idx b = do
    mary <- clone16 ary
    A.writeSmallArray mary idx b
    A.unsafeFreezeSmallArray mary
{-# inline update16M #-}

-- | /O(n)/ Update the element at the given position in this array, by applying a function to it.
update16With' :: A.SmallArray e -> Int -> (e -> e) -> A.SmallArray e
update16With' ary idx f = update16 ary idx $! f (A.indexSmallArray ary idx)
{-# inline update16With' #-}

-- | Unsafely clone an array of 16 elements.  The length of the input
-- array is not checked.
clone16 :: A.SmallArray e -> ST s (A.SmallMutableArray s e)
clone16 ary =
    A.thawSmallArray ary 0 16

------------------------------------------------------------------------
-- Bit twiddling

bitsPerSubkey :: Int
bitsPerSubkey = 4

maxChildren :: Int
maxChildren = fromIntegral $ 1 `unsafeShiftL` bitsPerSubkey

subkeyMask :: Bitmap
subkeyMask = 1 `unsafeShiftL` bitsPerSubkey - 1

sparseIndex :: Bitmap -> Bitmap -> Int
sparseIndex b m = popCount (b .&. (m - 1))

mask :: Int -> Shift -> Bitmap
mask w s = 1 `unsafeShiftL` index w s
{-# inline mask #-}

-- | Mask out the 'bitsPerSubkey' bits used for indexing at this level
-- of the tree.
index :: Int -> Shift -> Int
index w s = fromIntegral $ (unsafeShiftR (fromIntegral w) s) .&. subkeyMask
{-# inline index #-}

-- | A bitmask with the 'bitsPerSubkey' least significant bits set.
fullNodeMask :: Bitmap
fullNodeMask = complement (complement 0 `unsafeShiftL` maxChildren)
{-# inline fullNodeMask #-}

-- | Check if two the two arguments are the same value.  N.B. This
-- function might give false negatives (due to GC moving objects.)
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y ==# 1#)
{-# inline ptrEq #-}

------------------------------------------------------------------------
-- IsList instance
instance Exts.IsList (UnorderedIntMap v) where
    type Item (UnorderedIntMap v) = (Int, v)
    fromList = fromList
    toList   = toList

unsafeShiftL :: Word -> Int -> Word
unsafeShiftL (W# x#) (I# i#) = W# (x# `uncheckedShiftL#` i#)
{-# inline unsafeShiftL #-}

unsafeShiftR :: Word -> Int -> Word
unsafeShiftR (W# x#) (I# i#) = W# (x# `uncheckedShiftRL#` i#)
{-# inline unsafeShiftR #-}