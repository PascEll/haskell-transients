{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}

module ArrayCheck where

import Control.Monad.Primitive
import Data.Primitive
import GHC.Exts

foreign import prim "checkSmallMutableArrayzh" unsafeCheckSmallMutableArray# :: SmallMutableArray# s a -> State# s -> (# State# s, Int# #)

-- | This returns 'True' if the 'SmallMutableArray' is unfrozen and can still be mutated.
unsafeCheckSmallMutableArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> m Bool
unsafeCheckSmallMutableArray (SmallMutableArray m) = primitive $ \s -> case unsafeCheckSmallMutableArray# m s of
  (# s', i #) -> (# s', isTrue# i #)
