{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType #-}

module LinearUtils
  ( (&),
    Ur (..),
  )
where

import GHC.Exts

(&) :: forall {rep} a (b :: TYPE rep) p q. a %p -> (a %p -> b) %q -> b
x & f = f x

infixl 1 & -- same fixity as base.&

data Ur a where
  Ur :: a -> Ur a
