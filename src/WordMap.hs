{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module WordMap
  ( Key,
    WordMap,
    transient,
    lookup,
    lookupLT,
    insert,
    extendFromAscList,
    delete,
    union,
    empty,
    fromList,
    fromAscList,
    toList,
    TWordMap,
    persistent,
    lookupT,
    lookupLTT,
    insertT,
    extendFromAscListT,
    deleteT,
    unionT,
    emptyT,
    fromListT,
    fromAscListT,
    toListT,
  )
where

import ArrayCheck
import Control.Exception
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Bits
import Data.Primitive hiding (fromList)
import Data.Word
import qualified GHC.Exts
import Unsafe.Coerce
import Prelude hiding (lookup)
import GHC.Exts (sameSmallMutableArray#, reallyUnsafePtrEquality#, isTrue#)

samePtr :: a -> a -> Bool
samePtr !a !b =
  isTrue# (reallyUnsafePtrEquality# a b)
{-# INLINE samePtr #-}

sameSmallMutableArray :: SmallMutableArray s a -> SmallMutableArray s a -> Bool
sameSmallMutableArray (SmallMutableArray a) (SmallMutableArray b) =
  isTrue# (sameSmallMutableArray# a b)
{-# INLINE sameSmallMutableArray #-}

type Mask = Word16

type Key = Word64

type Offset = Int

newtype WordMap a = WordMap (Node a)

newtype TWordMap s a = TWordMap (TNode s a)

data Node a
  = Full {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallArray (Node a))
  | Partial {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallArray (Node a))
  | Tip {-# UNPACK #-} !Key a
  | Nil

data TNode s a
  = TFull {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallMutableArray s (TNode s a))
  | TPartial {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallMutableArray s (TNode s a))
  | TTip {-# UNPACK #-} !Key a
  | TNil

type Children s a = SmallMutableArray s (TNode s a)

class Hint h where
  apply :: h -> SmallMutableArray s a -> ST s ()

data Cold = Cold

data Warm = Warm

instance Hint Cold where
  apply _ array = void (unsafeFreezeSmallArray array)

instance Hint Warm where
  apply _ array = return ()

transient :: WordMap a -> TWordMap s a
transient = unsafeCoerce
{-# INLINE transient #-}

persistent :: TWordMap s a -> ST s (WordMap a)
persistent (TWordMap transientNode) = stToPrim $ do
  freezeArrays transientNode
  return $! WordMap $ unsafeCoerce transientNode
{-# INLINE persistent #-}

freezeArrays :: TNode s a -> ST s ()
freezeArrays (TFull _ _ children) = freezeArraysHelper children (sizeofSmallMutableArray children)
freezeArrays (TPartial _ _ mask children) =
  let length = popCount mask
   in freezeArraysHelper children length
freezeArrays (TTip _ _) = return ()
freezeArrays TNil = return ()
{-# INLINE freezeArrays #-}

freezeArraysHelper :: SmallMutableArray s (TNode s a) -> Int -> ST s ()
freezeArraysHelper children length = do
  is_mutable <- unsafeCheckSmallMutableArray children
  when is_mutable $ do
    forM_ [0 .. length - 1] $ \index -> do
      child <- readSmallArray children index
      freezeArrays child
    unsafeFreezeSmallArray children
    return ()
{-# INLINE freezeArraysHelper #-}

lookup :: Key -> WordMap a -> Maybe a
lookup key map = runST $ lookupT key (transient map)
{-# INLINE lookup #-}

lookupT :: Key -> TWordMap s a -> ST s (Maybe a)
lookupT key (TWordMap node) = lookupTNode key node
{-# INLINE lookupT #-}

lookupTNode :: Key -> TNode s a -> ST s (Maybe a)
lookupTNode !key = go
  where
    go TNil = return Nothing
    go (TTip prefix value)
      | key == prefix = return $ Just value
      | otherwise = return Nothing
    go (TFull prefix offset children)
      | index <= 0xf = readSmallArray children index >>= go
      | otherwise = return Nothing
      where
        index = childIndex key prefix offset
    go (TPartial prefix offset mask children)
      | childIdx <= 0xf && testBit mask childIdx = readSmallArray children arrayIdx >>= go
      | otherwise = return Nothing
      where
        childIdx = childIndex key prefix offset
        arrayIdx = arrayIndex mask childIdx
{-# INLINE lookupTNode #-}

lookupLT :: Key -> WordMap a -> Maybe (Key, a)
lookupLT key map = runST $ lookupLTT key (transient map)
{-# INLINE lookupLT #-}

lookupLTT :: Key -> TWordMap s a -> ST s (Maybe (Key, a))
lookupLTT key (TWordMap node) = lookupLTTNode key node
{-# INLINE lookupLTT #-}

lookupLTTNode :: Key -> TNode s a -> ST s (Maybe (Key, a))
lookupLTTNode !key = go
  where
    go TNil = return Nothing
    go (TTip prefix value)
      | prefix >= key = return Nothing
      | otherwise = return $ Just (prefix, value)
    go (TFull prefix offset children)
      | prefix >= key = return Nothing
      | index > 0xf = readSmallArray children 0xf >>= lookupMaxTNode
      | otherwise = go' children index
      where
        index = childIndex key prefix offset
    go (TPartial prefix offset mask children)
      | prefix >= key = return Nothing
      | childIdx > 0xf = readSmallArray children (length - 1) >>= lookupMaxTNode
      | not (testBit mask childIdx) =
        if arrayIdx > 0
          then readSmallArray children (arrayIdx - 1) >>= lookupMaxTNode
          else return Nothing
      | otherwise = go' children arrayIdx
      where
        childIdx = childIndex key prefix offset
        arrayIdx = arrayIndex mask childIdx
        length = popCount mask

    go' children index = do
      result <- readSmallArray children index >>= go
      case result of
        Just kv -> return $ Just kv
        Nothing ->
          if index > 0
            then readSmallArray children (index - 1) >>= lookupMaxTNode
            else return Nothing
{-# INLINE lookupLTTNode #-}

lookupMaxTNode :: TNode s a -> ST s (Maybe (Key, a))
lookupMaxTNode = go
  where
    go TNil = return Nothing
    go (TTip prefix value) = return $ Just (prefix, value)
    go (TFull prefix offset children) = readSmallArray children 0xf >>= go
    go (TPartial prefix offset mask children) =
      let length = popCount mask
       in readSmallArray children (length - 1) >>= go

insert :: Key -> a -> WordMap a -> WordMap a
insert key value map = runST $ insertWithHint Cold key value (transient map) >>= persistent
{-# INLINE insert #-}

insertT :: Key -> a -> TWordMap s a -> ST s (TWordMap s a)
insertT = insertWithHint Warm
{-# INLINE insertT #-}

insertWithHint :: (Hint h) => h -> Key -> a -> TWordMap s a -> ST s (TWordMap s a)
insertWithHint hint key value (TWordMap node) = TWordMap <$> insertTNode hint key value node
{-# INLINE insertWithHint #-}

insertTNode :: (Hint h) => h -> Key -> a -> TNode s a -> ST s (TNode s a)
insertTNode hint = insertTNodeWith hint const
{-# INLINE insertTNode #-}

insertTNodeIfNotPresent :: (Hint h) => h -> Key -> a -> TNode s a -> ST s (TNode s a)
insertTNodeIfNotPresent hint = insertTNodeWith hint (\new_value old_value -> old_value)
{-# INLINE insertTNodeIfNotPresent #-}

insertTNodeWith ::
  (Hint h) =>
  h ->
  (a -> a -> a) ->
  Key ->
  a ->
  TNode s a ->
  ST s (TNode s a)
insertTNodeWith hint f = go
  where
    go !key value TNil = return $ TTip key value
    go key value node@(TTip prefix old_value)
      | key == prefix = return $ TTip key (f value old_value)
      | otherwise = link hint node (TTip key value)
    go key value node@(TFull prefix offset children)
      | index <= 0xf = do
        !newChildren <- updateChildWith hint (go key value) children index
        if sameSmallMutableArray children newChildren
          then return node
          else return $ TFull prefix offset newChildren
      | otherwise = link hint node (TTip key value)
      where
        index = childIndex key prefix offset
    go key value node@(TPartial prefix offset mask children)
      | childIdx > 0xf = link hint node (TTip key value)
      | testBit mask childIdx = do
        !newChildren <- updateChildWith hint (go key value) children arrayIdx
        if sameSmallMutableArray children newChildren
          then return node
          else return $ TPartial prefix offset mask newChildren
      | otherwise = do
        let child = TTip key value
        !newChildren <- insertSmallMutableArrayAndApplyHint hint children length arrayIdx child
        return $! makeTNode prefix offset (setBit mask childIdx) newChildren
      where
        childIdx = childIndex key prefix offset
        arrayIdx = arrayIndex mask childIdx
        length = popCount mask
{-# INLINE insertTNodeWith #-}

extendFromAscList :: [(Key, a)] -> WordMap a -> WordMap a
extendFromAscList xs map = runST $ extendFromAscListWithHint Cold xs (transient map) >>= persistent
{-# INLINE extendFromAscList #-}

extendFromAscListT :: [(Key, a)] -> TWordMap s a -> ST s (TWordMap s a)
extendFromAscListT = extendFromAscListWithHint Warm
{-# INLINE extendFromAscListT #-}

extendFromAscListWithHint ::
  (Hint h) =>
  h ->
  [(Key, a)] ->
  TWordMap s a ->
  ST s (TWordMap s a)
extendFromAscListWithHint hint xs (TWordMap node) = TWordMap <$> extendFromAscListTNode hint xs node
{-# INLINE extendFromAscListWithHint #-}

extendFromAscListTNode :: (Hint h) => h -> [(Key, a)] -> TNode s a -> ST s (TNode s a)
extendFromAscListTNode hint [] node = return $! node
extendFromAscListTNode hint ((k, v) : xs) TNil = extendFromAscListTNode hint xs (TTip k v)
extendFromAscListTNode hint xs node = go xs node
  where
    go xs node = do
      (!node, rest) <- insertAllInSubtree hint xs node
      case rest of
        [] -> return node
        (k, v) : rest' -> link hint node (TTip k v) >>= go rest'
{-# INLINE extendFromAscListTNode #-}

insertAllInSubtree ::
  (Hint h) =>
  h ->
  [(Key, a)] ->
  TNode s a ->
  ST s (TNode s a, [(Key, a)])
insertAllInSubtree hint kvs node = case node of
  TTip key value
    | ((k, v) : rest) <- kvs, key == k -> return (TTip key v, rest)
    | otherwise -> return (node, kvs)
  TFull prefix offset children -> insertIntoFull prefix offset children kvs
  TPartial prefix offset mask children -> insertIntoPartial prefix offset mask children kvs
  TNil -> undefined
  where
    insertIntoFull prefix offset children [] = do
      apply hint children
      let !node = TFull prefix offset children
      return (node, [])
    insertIntoFull prefix offset children kvs@((k, v) : _)
      | index > 0xf = do
        apply hint children
        let !node = TFull prefix offset children
        return (node, kvs)
      | otherwise = do
        (newChildren, rest) <- insertIntoChild prefix offset children index index kvs
        insertIntoFull prefix offset newChildren rest
      where
        index = childIndex prefix k offset

    insertIntoPartial prefix offset mask children [] = do
      apply hint children
      let !node = TPartial prefix offset mask children
      return (node, [])
    insertIntoPartial prefix offset mask children kvs@((k, v) : _)
      | childIdx > 0xf = apply hint children >> return (TPartial prefix offset mask children, kvs)
      | testBit mask childIdx = do
        (!newChildren, rest) <- insertIntoChild prefix offset children childIdx arrayIdx kvs
        insertIntoPartial prefix offset mask newChildren rest
      | otherwise = do
        let child = TTip k v
        !newChildren <- insertSmallMutableArray children length arrayIdx child
        insertAllInSubtree hint (tail kvs) $! makeTNode prefix offset (setBit mask childIdx) newChildren
      where
        childIdx = childIndex prefix k offset
        arrayIdx = arrayIndex mask childIdx
        length = popCount mask

    insertIntoChild prefix offset children childIdx arrayIdx kvs = do
      child <- readSmallArray children arrayIdx
      (newChild, rest) <- insertAllInSubtree hint kvs child
      (newChild', rest') <- case rest of
        ((k, v) : rest')
          | childIndex prefix k offset == childIdx -> (\node -> (node, rest')) <$> link hint newChild (TTip k v)
        _ -> pure (newChild, rest)
      !newChildren <- updateChild hint children arrayIdx newChild'
      return (newChildren, rest')

delete :: Key -> WordMap a -> WordMap a
delete key map = runST $ deleteWithHint Cold key (transient map) >>= persistent
{-# INLINE delete #-}

deleteT :: Key -> TWordMap s a -> ST s (TWordMap s a)
deleteT = deleteWithHint Warm
{-# INLINE deleteT #-}

deleteWithHint :: (Hint h) => h -> Key -> TWordMap s a -> ST s (TWordMap s a)
deleteWithHint hint key (TWordMap node) = TWordMap <$> deleteTNode hint key node
{-# INLINE deleteWithHint #-}

deleteTNode :: (Hint h) => h -> Key -> TNode s a -> ST s (TNode s a)
deleteTNode hint key = go
  where
    go TNil = return TNil
    go node@(TTip prefix _)
      | key == prefix = return TNil
      | otherwise = return node
    go node@(TFull prefix offset children)
      | index <= 0xf = do
        newChild <- readSmallArray children index >>= go
        case newChild of
          TNil -> do
            newChildren <- deleteSmallMutableArrayAndApplyHint hint children index
            return $! TPartial prefix offset (complement (bit index)) newChildren
          _ -> do
            newChildren <- updateChild hint children index newChild
            if sameSmallMutableArray children newChildren
              then return node
              else return $ TFull prefix offset newChildren
      | otherwise = return node
      where
        index = childIndex key prefix offset
    go node@(TPartial prefix offset mask children)
      | childIdx <= 0xf && testBit mask childIdx = do
        newChild <- readSmallArray children arrayIdx >>= go
        case newChild of
          TNil
            | sizeofSmallMutableArray children == 2 -> readSmallArray children ((arrayIdx + 1) .&. 1)
            | otherwise -> do
              newChildren <- deleteSmallMutableArrayAndApplyHint hint children arrayIdx
              return $ TPartial prefix offset (clearBit mask childIdx) newChildren
          _ -> do
            newChildren <- updateChild hint children arrayIdx newChild
            if sameSmallMutableArray children newChildren
              then return node
              else return $ TPartial prefix offset mask newChildren
      | otherwise = return node
      where
        childIdx = childIndex key prefix offset
        arrayIdx = arrayIndex mask childIdx
{-# INLINE deleteTNode #-}

union :: WordMap a -> WordMap a -> WordMap a
union map1 map2 = runST $ unionWithHint Cold (transient map1) (transient map2) >>= persistent
{-# INLINE union #-}

unionT :: TWordMap s a -> TWordMap s a -> ST s (TWordMap s a)
unionT = unionWithHint Warm
{-# INLINE unionT #-}

unionWithHint ::
  (Hint h) =>
  h ->
  TWordMap s a ->
  TWordMap s a ->
  ST s (TWordMap s a)
unionWithHint hint (TWordMap node1) (TWordMap node2) = TWordMap <$> unionTNode hint node1 node2
{-# INLINE unionWithHint #-}

unionTNode :: (Hint h) => h -> TNode s a -> TNode s a -> ST s (TNode s a)
unionTNode _ node1 TNil = return node1
unionTNode _ TNil node2 = return node2
unionTNode hint (TTip prefix1 value1) node2 = insertTNode hint prefix1 value1 node2
unionTNode hint node1 (TTip prefix2 value2) = insertTNodeIfNotPresent hint prefix2 value2 node1
unionTNode hint node1 node2
  | shorter offset1 offset2 = union1
  | shorter offset2 offset1 = union2
  | prefix1 /= prefix2 = link hint node1 node2
  | otherwise = unionChildren
  where
    (prefix1, offset1, mask1, children1) = case node1 of
      TFull prefix offset children -> (prefix, offset, complement zeroBits, children)
      TPartial prefix offset mask children -> (prefix, offset, mask, children)
      _ -> undefined

    (prefix2, offset2, mask2, children2) = case node2 of
      TFull prefix offset children -> (prefix, offset, complement zeroBits, children)
      TPartial prefix offset mask children -> (prefix, offset, mask, children)
      _ -> undefined

    shorter offset1 offset2 = offset1 > offset2

    union1
      | childIdx > 0xf = link hint node1 node2
      | testBit mask1 childIdx = do
        newChildren <- updateChildWith hint (\child -> unionTNode hint child node2) children1 arrayIdx
        return $! makeTNode prefix1 offset1 mask1 newChildren
      | otherwise = do
        newChildren <- insertSmallMutableArrayAndApplyHint hint children1 length arrayIdx node2
        return $! makeTNode prefix1 offset1 (setBit mask1 childIdx) newChildren
      where
        childIdx = childIndex prefix2 prefix1 offset1
        arrayIdx = arrayIndex mask1 childIdx
        length = popCount mask1

    union2
      | childIdx > 0xf = link hint node1 node2
      | testBit mask2 childIdx = do
        newChildren <- updateChildWith hint (\child -> unionTNode hint node1 child) children2 arrayIdx
        return $! makeTNode prefix2 offset2 mask2 newChildren
      | otherwise = do
        newChildren <- insertSmallMutableArrayAndApplyHint hint children2 length arrayIdx node1
        return $! makeTNode prefix2 offset2 (setBit mask2 childIdx) newChildren
      where
        childIdx = childIndex prefix1 prefix2 offset2
        arrayIdx = arrayIndex mask2 childIdx
        length = popCount mask2

    unionChildren = do
      isMutable1 <- unsafeCheckSmallMutableArray children1
      if isMutable1 && maskIsSubset mask2 mask1
        then unionInto1
        else do
          isMutable2 <- unsafeCheckSmallMutableArray children2
          if isMutable2 && maskIsSubset mask1 mask2
            then unionInto2
            else newSmallArray newChildrenCount undefined >>= unionIntoNew

    maskIsSubset mask1 mask2 = (mask2 .|. complement mask1) == complement zeroBits
    newMask = mask1 .|. mask2
    newChildrenCount = popCount newMask

    unionInto1 = do
      go 15 (childrenCount1 - 1) (childrenCount2 - 1)
      return $! makeTNode prefix1 offset1 mask1 children1
      where
        go childIdx arrayIdx1 0
          | testBit mask2 childIdx = unionChildrenElements children1 arrayIdx1 children2 0 children1 arrayIdx1
          | otherwise = return ()
        go childIdx arrayIdx1 arrayIdx2
          | testBit mask2 childIdx = do
            unionChildrenElements children1 arrayIdx1 children2 arrayIdx2 children1 arrayIdx1
            go (childIdx - 1) (arrayIdx1 - 1) (arrayIdx2 - 1)
          | otherwise = go (childIdx - 1) (arrayIdx1 - 1) arrayIdx2

    unionInto2 = do
      go 15 (childrenCount1 - 1) (childrenCount2 - 1)
      return $! makeTNode prefix2 offset2 mask2 children2
      where
        go childIdx 0 arrayIdx2
          | testBit mask1 childIdx = unionChildrenElements children1 0 children2 arrayIdx2 children2 arrayIdx2
          | otherwise = return ()
        go childIdx arrayIdx1 arrayIdx2
          | testBit mask1 childIdx = do
            unionChildrenElements children1 arrayIdx1 children2 arrayIdx2 children2 arrayIdx2
            go (childIdx - 1) (arrayIdx1 - 1) (arrayIdx2 - 1)
          | otherwise = go (childIdx - 1) arrayIdx1 (arrayIdx2 - 1)

    unionIntoNew newChildren = do
      go 15 (childrenCount1 - 1) (childrenCount2 - 1) (newChildrenCount - 1)
      apply hint newChildren
      return $! makeTNode prefix1 offset1 newMask newChildren
      where
        go childIdx arrayIdx1 arrayIdx2 0
          | present1 && present2 = unionChildrenElements children1 arrayIdx1 children2 arrayIdx2 newChildren 0
          | present1 = copySmallMutableArray newChildren 0 children1 arrayIdx1 1
          | present2 = copySmallMutableArray newChildren 0 children2 arrayIdx2 1
          | otherwise = go (childIdx - 1) arrayIdx1 arrayIdx2 0
          where
            !present1 = testBit mask1 childIdx
            !present2 = testBit mask2 childIdx
        go childIdx arrayIdx1 arrayIdx2 arrayIdxNew
          | present1 && present2 = do
            unionChildrenElements children1 arrayIdx1 children2 arrayIdx2 newChildren arrayIdxNew
            go (childIdx - 1) (arrayIdx1 - 1) (arrayIdx2 - 1) (arrayIdxNew - 1)
          | present1 = do
            copySmallMutableArray newChildren arrayIdxNew children1 arrayIdx1 1
            go (childIdx - 1) (arrayIdx1 - 1) arrayIdx2 (arrayIdxNew - 1)
          | present2 = do
            copySmallMutableArray newChildren arrayIdxNew children2 arrayIdx2 1
            go (childIdx - 1) arrayIdx1 (arrayIdx2 - 1) (arrayIdxNew - 1)
          | otherwise = go (childIdx - 1) arrayIdx1 arrayIdx2 arrayIdxNew
          where
            !present1 = testBit mask1 childIdx
            !present2 = testBit mask2 childIdx

    unionChildrenElements children1 arrayIdx1 children2 arrayIdx2 newChildren arrayIdxNew = do
      child1 <- readSmallArray children1 arrayIdx1
      child2 <- readSmallArray children2 arrayIdx2
      newChild <- unionTNode hint child1 child2
      writeSmallArray newChildren arrayIdxNew newChild

    childrenCount1 = popCount mask1
    childrenCount2 = popCount mask2

empty :: WordMap a
empty = WordMap emptyNode
{-# INLINE empty #-}

emptyNode :: Node a
emptyNode = Nil
{-# INLINE emptyNode #-}

emptyT :: TWordMap s a
emptyT = TWordMap emptyTNode
{-# INLINE emptyT #-}

emptyTNode :: TNode s a
emptyTNode = TNil
{-# INLINE emptyTNode #-}

fromList :: [(Key, a)] -> WordMap a
fromList xs = runST $ fromListT xs >>= persistent
{-# INLINE fromList #-}

fromListT :: [(Key, a)] -> ST s (TWordMap s a)
fromListT xs = do
  foldM (\map (k, v) -> insertT k v map) emptyT xs
{-# INLINE fromListT #-}

fromAscList :: [(Key, a)] -> WordMap a
fromAscList xs = extendFromAscList xs empty
{-# INLINE fromAscList #-}

fromAscListT :: [(Key, a)] -> ST s (TWordMap s a)
fromAscListT xs = extendFromAscListT xs emptyT
{-# INLINE fromAscListT #-}

toList :: WordMap a -> [(Key, a)]
toList (WordMap node) = toListNode node
{-# INLINE toList #-}

toListT :: TWordMap s a -> ST s [(Key, a)]
toListT map = toList <$> persistent map
{-# INLINE toListT #-}

toListNode :: Node a -> [(Key, a)]
toListNode Nil = []
toListNode (Tip prefix value) = [(prefix, value)]
toListNode (Full prefix offset children) = concatMap toListNode children
toListNode (Partial prefix offset mask children) = go 0
  where
    length = popCount mask
    go i
      | i == length = []
      | otherwise =
        let child = indexSmallArray children i
         in toListNode child ++ go (i + 1)

updateChildWith ::
  (Hint h) =>
  h ->
  (TNode s a -> ST s (TNode s a)) ->
  Children s a ->
  Int ->
  ST s (Children s a)
updateChildWith hint f children index = do
  child <- readSmallArray children index
  newChild <- f child
  if samePtr child newChild
    then apply hint children >> return children
    else updateChild hint children index newChild
{-# INLINE updateChildWith #-}

updateChild ::
  (Hint h) =>
  h ->
  Children s a ->
  Int ->
  TNode s a ->
  ST s (Children s a)
updateChild hint children index newChild = do
  isMutable <- unsafeCheckSmallMutableArray children
  newChildren <-
    if isMutable
      then pure children
      else cloneSmallMutableArray children 0 (sizeofSmallMutableArray children)
  writeSmallArray newChildren index newChild
  apply hint newChildren
  return newChildren
{-# INLINE updateChild #-}

makeTNode :: Key -> Offset -> Mask -> SmallMutableArray s (TNode s a) -> TNode s a
makeTNode prefix offset mask children
  | mask == maxBound = TFull prefix offset children
  | otherwise = TPartial prefix offset mask children
{-# INLINE makeTNode #-}

childIndex :: Key -> Key -> Offset -> Int
childIndex key prefix offset = fromIntegral $ unsafeShiftR (xor key prefix) offset
{-# INLINE childIndex #-}

arrayIndex :: Mask -> Int -> Int
arrayIndex mask childIndex = popCount (mask .&. (bit childIndex - 1))
{-# INLINE arrayIndex #-}

link :: (Hint h) => h -> TNode s a -> TNode s a -> ST s (TNode s a)
link hint node1 node2 = do
  let prefix1 = nodePrefix node1
  let prefix2 = nodePrefix node2

  let offset = branchOffset prefix1 prefix2
  let newPrefix = prefix1 .&. unsafeShiftL (complement (unsafeShiftL 1 offset - 1)) 4
  let childIdx1 = fromIntegral $ unsafeShiftR prefix1 offset .&. 0xf
  let childIdx2 = fromIntegral $ unsafeShiftR prefix2 offset .&. 0xf

  children <- newSmallArray 2 node1
  if childIdx1 < childIdx2
    then writeSmallArray children 1 node2
    else writeSmallArray children 0 node2
  apply hint children

  return $! TPartial newPrefix offset (bit childIdx1 .|. bit childIdx2) children
  where
    nodePrefix TNil = undefined
    nodePrefix (TTip prefix _) = prefix
    nodePrefix (TFull prefix _ _) = prefix
    nodePrefix (TPartial prefix _ _ _) = prefix
{-# INLINE link #-}

branchOffset :: Key -> Key -> Offset
branchOffset prefix1 prefix2 =
  assert (prefix1 /= prefix2) $
    (63 - countLeadingZeros (xor prefix1 prefix2)) .&. complement 0x3
{-# INLINE branchOffset #-}

insertSmallMutableArrayAndApplyHint ::
  (Hint h) =>
  h ->
  SmallMutableArray s a ->
  Int ->
  Int ->
  a ->
  ST s (SmallMutableArray s a)
insertSmallMutableArrayAndApplyHint hint array length index element = do
  new <- insertSmallMutableArray array length index element
  apply hint new
  return $! new
{-# INLINE insertSmallMutableArrayAndApplyHint #-}

insertSmallMutableArray ::
  SmallMutableArray s a ->
  Int ->
  Int ->
  a ->
  ST s (SmallMutableArray s a)
insertSmallMutableArray array length index element = do
  isMutable <- unsafeCheckSmallMutableArray array
  if (length < capacity) && isMutable
    then insertInPlace
    else copyAndInsert
  where
    capacity = sizeofSmallMutableArray array

    insertInPlace = do
      moveElements
      writeSmallArray array index element
      return array

    copyAndInsert = do
      let newCapacity = min 16 ((capacity * 3 + 1) `div` 2)
      new <- newSmallArray newCapacity undefined
      copySmallMutableArray new 0 array 0 index
      copySmallMutableArray new (index + 1) array index (length - index)
      writeSmallArray new index element
      return $! new

    moveElements = when (length > 0 && index < length) $ go (length - 1)
      where
        go i
          | i == index = readSmallArray array i >>= writeSmallArray array (i + 1)
          | otherwise = readSmallArray array i >>= writeSmallArray array (i + 1) >> go (i - 1)
{-# INLINE insertSmallMutableArray #-}

deleteSmallMutableArrayAndApplyHint ::
  (Hint h) =>
  h ->
  SmallMutableArray s a ->
  Int ->
  ST s (SmallMutableArray s a)
deleteSmallMutableArrayAndApplyHint hint old index = do
  new <- deleteSmallMutableArray old index
  apply hint new
  return $! new
{-# INLINE deleteSmallMutableArrayAndApplyHint #-}

deleteSmallMutableArray ::
  SmallMutableArray s a ->
  Int ->
  ST s (SmallMutableArray s a)
deleteSmallMutableArray array index = do
  isMutable <- unsafeCheckSmallMutableArray array
  if isMutable
    then deleteInPlace >> return array
    else copyAndDelete
  where
    capacity = sizeofSmallMutableArray array

    deleteInPlace = go index
      where
        go i
          | i == (capacity - 1) = writeSmallArray array i undefined
          | otherwise = readSmallArray array (i + 1) >>= writeSmallArray array i >> go (i + 1)

    copyAndDelete = do
      new <- newSmallArray capacity undefined
      copySmallMutableArray new 0 array 0 index
      copySmallMutableArray new index array (index + 1) (capacity - index - 1)
      return $! new
{-# INLINE deleteSmallMutableArray #-}
