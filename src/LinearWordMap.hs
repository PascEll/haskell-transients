{-# LANGUAGE LinearTypes #-}

module LinearWordMap
  ( LWordMap,
    transientL,
    persistentL,
    insertL,
    lookupL,
  )
where

import Control.Monad.ST
import LinearUtils
import System.IO.Unsafe
import Unsafe.Coerce
import WordMap

newtype LWordMap a = LWordMap (TWordMap RealWorld a)

toLinear :: (a -> b) -> (a %1 -> b)
toLinear = unsafeCoerce

transientL :: WordMap a -> (LWordMap a %1 -> Ur b) %1 -> Ur b
transientL map f = f (LWordMap (transient map))
{-# INLINE transientL #-}

persistentL :: LWordMap a %1 -> Ur (WordMap a)
persistentL = toLinear go
  where
    go (LWordMap map) = Ur $ unsafePerformIO $ stToIO $ persistent map
{-# INLINE persistentL #-}

insertL :: Key -> a -> LWordMap a %1 -> LWordMap a
insertL key value = toLinear go
  where
    go (LWordMap map) = LWordMap $ unsafePerformIO $ stToIO $ insertT key value map
{-# INLINE insertL #-}

deleteL :: Key -> LWordMap a %1 -> LWordMap a
deleteL key = toLinear go
  where
    go (LWordMap map) = LWordMap $ unsafePerformIO $ stToIO $ deleteT key map
{-# INLINE deleteL #-}

lookupL :: Key -> LWordMap a %1 -> (Ur (Maybe a), LWordMap a)
lookupL key = toLinear go
  where
    go (LWordMap map) =
      let mbValue = unsafePerformIO $ stToIO $ lookupT key map
       in (Ur mbValue, LWordMap map)
{-# INLINE lookupL #-}

fromListL :: [(Key, a)] -> (LWordMap a %1 -> Ur b) %1 -> Ur b
fromListL xs f = f (LWordMap map)
  where
    map = unsafePerformIO $ stToIO $ fromListT xs
{-# INLINE fromListL #-}
