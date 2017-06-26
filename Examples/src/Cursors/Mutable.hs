-- | Cursors into byte-addressed memory that allow type-safe writing
-- and reading of serialized data.
-- 
-- Requires the "linear-types" branch of GHC from the tweag.io fork.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}

module Cursors.Mutable
    ( -- * Cursors, with their implementation revealed:
      Has(..), Needs(..), Packed
      -- * Public cursor interface
    , writeC, readC, fstC, rstC, fstCM, fromHas, toHas
    , finish, withOutput, withC, withC2
    , tup, untup

      -- * Unsafe interface
    , unsafeCastNeeds, unsafeCastHas
    )
    where      

import Linear.Std
import qualified ByteArray as ByteArray

import Control.DeepSeq
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import Data.Int
import Foreign.Storable
import Prelude hiding (($))

-- Hard-coded constant:
--------------------------------------------------------------------------------
-- | Size allocated for each regions: 4KB.
regionSize :: Int
regionSize =
  -- 4096 -- in Bytes
  500 * 1000*1000

-- Cursor Types:
--------------------------------------------------------------------------------

-- | A "needs" cursor requires a list of fields be written to the
-- bytestream before the data is fully initialized.  Once it is, a
-- value of the (second) type parameter can be extracted.
newtype Needs (l :: [*]) t = Needs ByteArray.WByteArray

-- | A "has" cursor is a pointer to a series of consecutive,
-- serialized values.  It can be read multiple times.
newtype Has (l :: [*]) = Has ByteString
  deriving Show

-- | A packed value is very like a singleton Has cursor.  It
-- represents a dense encoding of a single value of the type `a`.
newtype Packed a = Packed ByteString
  deriving (Show,Eq)

instance NFData (Packed a) where
  rnf (Packed !_) = ()

           
-- Cursor interface
--------------------------------------------------------------------------------

{-# INLINABLE writeC #-}           
{-# INLINABLE fromHas #-}
{-# INLINABLE toHas #-}
{-# INLINE unsafeCastNeeds #-}
{-# INLINE unsafeCastHas #-}
{-# INLINABLE finish #-}
{-# INLINABLE untup #-}
{-# INLINABLE tup #-}
{-# INLINABLE withOutput #-}

-- | Write a value to the cursor.  Write doesn't need to be linear in
-- the value written, because that value is serialized and copied.
writeC :: Storable a => a -> Needs (a ': rst) t ⊸ Needs rst t
writeC a (Needs bld1) = Needs (ByteArray.writeStorable a bld1)

{-# INLINE readC #-}
-- | Reading from a cursor scrolls past the read item and gives a
-- cursor into the next element in the stream:
readC :: forall a rst . Storable a => Has (a ': rst) -> (a, Has rst)
readC (Has bs) =
    let !a = ByteArray.headStorable bs in 
    (a, Has (ByteString.drop (sizeOf (undefined::a)) bs))

{-# INLINE fstC #-}
-- | Equivalent to the first value returned by @readC@.
fstC :: forall a rst . Storable a => Has (a ': rst) -> a
fstC (Has bs) = ByteArray.headStorable bs

{-# INLINE rstC #-}
-- | Equivalent to the second value returned by @readC@.
rstC :: forall a rst . Storable a => Has (a ': rst) -> Has rst
rstC (Has bs) = Has (ByteString.drop (sizeOf (undefined::a)) bs)

{-# INLINE fstCM #-}
-- | Monadic version of @fstC@
fstCM :: forall a rst . Storable a => Has (a ': rst) -> ByteArray.ReadM a
fstCM (Has bs) = ByteArray.headStorableOfM bs

{-# INLINE withC #-}
withC :: forall a b rst . Storable a => Has (a ': rst) -> (a -> b) -> b
withC (Has bs) = ByteArray.withHeadStorable bs

{-# INLINE withC2 #-}
withC2 :: forall a b1 b2 rst . Storable a => Has (a ': rst) -> (a -> (# b1, b2 #)) -> (# b1, b2 #)
withC2 (Has bs) = ByteArray.withHeadStorable2 bs
                  
-- | Safely "cast" a has-cursor to a packed value.
fromHas :: Has '[a] ⊸ Packed a
fromHas (Has b) = Packed b

-- | Safely cast a packed value to a has cursor.
toHas :: Packed a ⊸ Has '[a]
toHas (Packed b) = Has b

-- | Perform an unsafe conversion reflecting knowledge about the
-- memory layout of a particular type (when packed).
unsafeCastNeeds :: Needs l1 a ⊸ Needs l2 a
unsafeCastNeeds (Needs b) = (Needs b)

unsafeCastHas :: Has l1 ⊸ Has l2
unsafeCastHas (Has b) = (Has b)

-- | "Cast" a fully-initialized write cursor into a read one.
finish :: Needs '[] a ⊸ Unrestricted (Has '[a])
finish (Needs bs) = Has `mapU` ByteArray.freeze bs

-- | We /could/ create a general approach to safe coercions for data
-- with the same serialized layout, analogous to, but distinct from,
-- the Coercable class.
untup :: Needs ((a,b) ': c) d ⊸ Needs (a ': b ': c) d
untup (Needs x) = Needs x

tup :: Needs (a ': b ': c) d ⊸ Needs ((a,b) ': c) d
tup (Needs x) = Needs x
                    
-- | Allocate a fresh output cursor and compute with it.
withOutput :: (Needs '[a] a ⊸ Unrestricted b) ⊸ Unrestricted b
withOutput fn = ByteArray.alloc regionSize $ \ bs -> fn (Needs bs)

-- Tests:
--------------------------------------------------------------------------------

foo :: Needs '[Int, Bool] Double
foo = undefined

bar :: Needs '[Bool] Double
bar = writeC 3 foo

_test01 :: Needs '[Int] a ⊸ Needs '[] a
_test01 x = writeC 3 x

test02 :: Needs '[] Double
test02 = writeC True bar

_test03 :: Double
_test03 = fst (readC (getUnrestricted (finish test02)))

