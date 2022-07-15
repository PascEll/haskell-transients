module WordMap
  ( WordMap,
    transient,
    lookup,
    insert,
    delete,
    empty,
    fromList,
    toList,
    TWordMap,
    persistent,
    lookupT,
    insertT,
    deleteT,
    emptyT,
    fromListT,
    toListT,
  )
where

import ArrayCheck
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Bits
import Data.Primitive hiding (fromList)
import Data.Word
import Unsafe.Coerce
import Prelude hiding (lookup)

type Mask = Word16

type Key = Word64

type Offset = Int

newtype WordMap a = WordMap (Node a) deriving (Eq, Show)

newtype TWordMap s a = TWordMap (TNode s a) deriving (Eq)

data Node a
  = Full {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallArray (Node a))
  | Partial {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallArray (Node a))
  | Tip {-# UNPACK #-} !Key a
  | Nil
  deriving (Eq, Show)

data TNode s a
  = TFull {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallMutableArray s (TNode s a))
  | TPartial {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallMutableArray s (TNode s a))
  | TTip {-# UNPACK #-} !Key a
  | TNil
  deriving (Eq)

type Children s a = SmallMutableArray s (TNode s a)

class Hint h where
  apply :: PrimMonad m => h -> SmallMutableArray (PrimState m) a -> m ()

data Cold = Cold

data Warm = Warm

instance Hint Cold where
  apply _ array = void (unsafeFreezeSmallArray array)

instance Hint Warm where
  apply _ array = return ()

transient :: WordMap a -> TWordMap s a
transient = unsafeCoerce
{-# INLINE transient #-}

persistent :: PrimMonad m => TWordMap (PrimState m) a -> m (WordMap a)
persistent (TWordMap transientNode) = do
  freezeArrays transientNode
  return $ WordMap $ unsafeCoerce transientNode
{-# INLINE persistent #-}

freezeArrays :: PrimMonad m => TNode (PrimState m) a -> m ()
freezeArrays (TFull _ _ children) = freezeArraysHelper children
freezeArrays (TPartial _ _ _ children) = freezeArraysHelper children
freezeArrays (TTip _ _) = return ()
freezeArrays TNil = return ()
{-# INLINE freezeArrays #-}

freezeArraysHelper :: PrimMonad m => SmallMutableArray (PrimState m) (TNode (PrimState m) a) -> m ()
freezeArraysHelper children = do
  is_mutable <- unsafeCheckSmallMutableArray children
  when is_mutable $ do
    forM_ [0 .. sizeofSmallMutableArray children - 1] $ \index -> do
      child <- readSmallArray children index
      freezeArrays child
    unsafeFreezeSmallArray children
    return ()
{-# INLINE freezeArraysHelper #-}

lookup :: Key -> WordMap a -> Maybe a
lookup key map = runST $ lookupT key (transient map)
{-# INLINE lookup #-}

lookupT :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (Maybe a)
lookupT key (TWordMap node) = lookupTNode key node
{-# INLINE lookupT #-}

lookupTNode :: PrimMonad m => Key -> TNode (PrimState m) a -> m (Maybe a)
lookupTNode _ TNil = return Nothing
lookupTNode key (TTip prefix value)
  | key == prefix = return $ Just value
  | otherwise = return Nothing
lookupTNode key (TFull prefix offset children)
  | index <= 0xf = lookupChild key children index
  | otherwise = return Nothing
  where
    index = childIndex key prefix offset
lookupTNode key (TPartial prefix offset mask children)
  | childIdx <= 0xf && testBit mask childIdx = lookupChild key children arrayIdx
  | otherwise = return Nothing
  where
    childIdx = childIndex key prefix offset
    arrayIdx = arrayIndex mask childIdx
{-# INLINE lookupTNode #-}

lookupChild key children index = do
  child <- readSmallArray children index
  lookupTNode key child
{-# INLINE lookupChild #-}

insert :: Key -> a -> WordMap a -> WordMap a
insert key value map = runST $ insertWithHint Cold key value (transient map) >>= persistent
{-# INLINE insert #-}

insertT :: PrimMonad m => Key -> a -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
insertT = insertWithHint Warm
{-# INLINE insertT #-}

insertWithHint :: (Hint h, PrimMonad m) => h -> Key -> a -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
insertWithHint hint key value (TWordMap node) = TWordMap <$> insertTNode Cold key value node
{-# INLINE insertWithHint #-}

insertTNode :: (Hint h, PrimMonad m) => h -> Key -> a -> TNode (PrimState m) a -> m (TNode (PrimState m) a)
insertTNode _ key value TNil = return $ TTip key value
insertTNode hint key value node@(TTip prefix _)
  | key == prefix = return $ TTip prefix value
  | otherwise = splitNode hint node key value
insertTNode hint key value node@(TFull prefix offset children)
  | index <= 0xf = do
    newChildren <- insertIntoChild hint key value children index
    return $ TFull prefix offset newChildren
  | otherwise = splitNode hint node key value
  where
    index = childIndex key prefix offset
insertTNode hint key value node@(TPartial prefix offset mask children)
  | childIdx > 0xf = splitNode hint node key value
  | testBit mask childIdx = do
    newChildren <- insertIntoChild hint key value children arrayIdx
    return $ TPartial prefix offset mask newChildren
  | otherwise = do
    let child = TTip key value
    newChildren <- insertSmallMutableArray children arrayIdx child
    apply hint newChildren
    return $ makeTNode prefix offset (setBit mask childIdx) newChildren
  where
    childIdx = childIndex key prefix offset
    arrayIdx = arrayIndex mask childIdx
{-# INLINE insertTNode #-}

insertIntoChild ::
  (Hint h, PrimMonad m) =>
  h ->
  Key ->
  a ->
  Children (PrimState m) a ->
  Int ->
  m (Children (PrimState m) a)
insertIntoChild hint key value children index = do
  child <- readSmallArray children index
  newChild <- insertTNode hint key value child
  updateChild hint children index newChild
{-# INLINE insertIntoChild #-}

splitNode :: (Hint h, PrimMonad m) => h -> TNode (PrimState m) a -> Key -> a -> m (TNode (PrimState m) a)
splitNode hint node key value = do
  let prefix = nodePrefix node

  let offset = (63 - countLeadingZeros (xor prefix key)) .&. complement 0x3
  let newPrefix = prefix .&. unsafeShiftL (complement (unsafeShiftL 1 offset - 1)) 4
  let childIdx1 = fromIntegral $ unsafeShiftR prefix offset .&. 0xf
  let childIdx2 = fromIntegral $ unsafeShiftR key offset .&. 0xf

  children <- newSmallArray 2 node
  let node2 = TTip key value
  if childIdx1 < childIdx2
    then writeSmallArray children 1 node2
    else writeSmallArray children 0 node2
  apply hint children

  return $ TPartial newPrefix offset (bit childIdx1 .|. bit childIdx2) children
{-# INLINE splitNode #-}

nodePrefix :: TNode s a -> Key
nodePrefix TNil = undefined
nodePrefix (TTip prefix _) = prefix
nodePrefix (TFull prefix _ _) = prefix
nodePrefix (TPartial prefix _ _ _) = prefix
{-# INLINE nodePrefix #-}

delete :: Key -> WordMap a -> WordMap a
delete key map = runST $ deleteWithHint Cold key (transient map) >>= persistent
{-# INLINE delete #-}

deleteT :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
deleteT = deleteWithHint Warm
{-# INLINE deleteT #-}

deleteWithHint :: (Hint h, PrimMonad m) => h -> Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
deleteWithHint hint key (TWordMap node) = TWordMap <$> deleteTNode Cold key node
{-# INLINE deleteWithHint #-}

deleteTNode :: (Hint h, PrimMonad m) => h -> Key -> TNode (PrimState m) a -> m (TNode (PrimState m) a)
deleteTNode _ _ TNil = return TNil
deleteTNode _ key node@(TTip prefix _)
  | key == prefix = return TNil
  | otherwise = return node
deleteTNode hint key node@(TFull prefix offset children)
  | index <= 0xf = do
    newChild <- deleteFromChild hint key children index
    case newChild of
      TNil -> do
        newChildren <- deleteFromChildren hint children index
        return $ TPartial prefix offset (complement (bit index)) newChildren
      _ -> do
        newChildren <- updateChild hint children index newChild
        return $ TFull prefix offset newChildren
  | otherwise = return node
  where
    index = childIndex key prefix offset
deleteTNode hint key node@(TPartial prefix offset mask children)
  | childIdx <= 0xf && testBit mask childIdx = do
    newChild <- deleteFromChild hint key children arrayIdx
    case newChild of
      TNil
        | sizeofSmallMutableArray children == 2 -> readSmallArray children ((arrayIdx + 1) .&. 1)
        | otherwise -> do
          newChildren <- deleteFromChildren hint children arrayIdx
          return $ TPartial prefix offset (clearBit mask childIdx) newChildren
      _ -> do
        newChildren <- updateChild hint children arrayIdx newChild
        return $ TPartial prefix offset mask newChildren
  | otherwise = return node
  where
    childIdx = childIndex key prefix offset
    arrayIdx = arrayIndex mask childIdx
{-# INLINE deleteTNode #-}

deleteFromChild :: (Hint h, PrimMonad m) => h -> Key -> Children (PrimState m) a -> Int -> m (TNode (PrimState m) a)
deleteFromChild hint key children index = do
  child <- readSmallArray children index
  deleteTNode hint key child
{-# INLINE deleteFromChild #-}

deleteFromChildren :: (Hint h, PrimMonad m) => h -> Children (PrimState m) a -> Int -> m (Children (PrimState m) a)
deleteFromChildren hint children arrayIdx = do
  newChildren <- deleteSmallMutableArray children arrayIdx
  apply hint newChildren
  return newChildren
{-# INLINE deleteFromChildren #-}

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

fromListT :: PrimMonad m => [(Key, a)] -> m (TWordMap (PrimState m) a)
fromListT xs = do
  foldM (\map (k, v) -> insertT k v map) emptyT xs
{-# INLINE fromListT #-}

toList :: WordMap a -> [(Key, a)]
toList (WordMap node) = toListNode node
{-# INLINE toList #-}

toListT :: PrimMonad m => TWordMap (PrimState m) a -> m [(Key, a)]
toListT map = toList <$> persistent map
{-# INLINE toListT #-}

toListNode :: Node a -> [(Key, a)]
toListNode Nil = []
toListNode (Tip prefix value) = [(prefix, value)]
toListNode (Full prefix offset children) = concatMap toListNode children
toListNode (Partial prefix offset mask children) = concatMap toListNode children
{-# INLINE toListNode #-}

updateChild ::
  (Hint h, PrimMonad m) =>
  h ->
  Children (PrimState m) a ->
  Int ->
  TNode (PrimState m) a ->
  m (Children (PrimState m) a)
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

insertSmallMutableArray ::
  PrimMonad m =>
  SmallMutableArray (PrimState m) a ->
  Int ->
  a ->
  m (SmallMutableArray (PrimState m) a)
insertSmallMutableArray old index element = do
  let oldSize = sizeofSmallMutableArray old
  new <- newSmallArray (oldSize + 1) element
  copySmallMutableArray new 0 old 0 index
  copySmallMutableArray new (index + 1) old index (oldSize - index)
  return new
{-# INLINE insertSmallMutableArray #-}

deleteSmallMutableArray ::
  PrimMonad m =>
  SmallMutableArray (PrimState m) a ->
  Int ->
  m (SmallMutableArray (PrimState m) a)
deleteSmallMutableArray old index = do
  let oldSize = sizeofSmallMutableArray old
  new <- newSmallArray (oldSize - 1) undefined
  copySmallMutableArray new 0 old 0 index
  copySmallMutableArray new index old (index + 1) (oldSize - index - 1)
  return new
{-# INLINE deleteSmallMutableArray #-}
