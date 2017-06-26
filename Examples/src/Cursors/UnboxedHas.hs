-- | A painfully low-level unboxed version of Has cursors.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Cursors.UnboxedHas
    (Has#, headInt, headWord8, unsafeCast)
   where

import GHC.Prim 
import GHC.Int
import GHC.Word
import Data.Kind(Type)
import Foreign.Storable(sizeOf)
----------------------------------------

-- | A raw position within a buffer being read.
type Has# (a :: [Type]) = Addr#

{-# INLINE headInt #-}
headInt :: Has# (Int ': r) -> (# Int, Has# r #)
headInt addr =
    (# I# (indexIntOffAddr# addr 0# )
    , plusAddr# addr szInt #)
 where
  !(I# szInt) = sizeOf (undefined::Int)

{-# INLINE headWord8 #-}
headWord8 :: Has# (Word8 ': r) -> (# Word8, Has# r #)
headWord8 addr =
  (# W8# (int2Word# (ord# (indexCharOffAddr# addr 0# )))
  , plusAddr# addr 1# #)

unsafeCast :: Has# a -> Has# b
unsafeCast h = h
