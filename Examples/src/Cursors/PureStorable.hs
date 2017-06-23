-- | A debugging aide.  A version of Cursors that uses the Storable
-- type class, but converts it into pure operations in the simplest
-- possible way.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Cursors.PureStorable
    ( -- * Abstract Cursor datatypes
      Has, Needs, Packed
      -- * Public cursor interface
    , writeC, readC, fromHas, toHas
    , finish, withOutput
    , tup, untup
      
      -- * Unsafe interface
    , unsafeCastNeeds, unsafeCastHas
    )
    where

import Linear.Std (Unrestricted(..)) -- linerror
import Linear.Unsafe (unsafeCastLinear, unsafeCastLinear2, unsafeUnrestricted)

import Control.DeepSeq
import Data.Sequence as Seq
import Data.Char (ord)
import Data.List as L
import Data.ByteString.Char8   as BS
import Data.ByteString.Internal (fromForeignPtr, toForeignPtr)
import Foreign.Storable
import Foreign.Ptr ()
import Foreign.ForeignPtr (ForeignPtr, withForeignPtr, mallocForeignPtr, castForeignPtr)
-- import Foreign.Marshal.Alloc (alloca)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Prelude as P 
--------------------------------------------------------------------------------

-- | A hack for treating Storable as a pure, rather than IO-based interface.
serialize :: Storable a => a ⊸ ByteString
serialize = unsafeCastLinear
 (\x -> unsafeDupablePerformIO $ do
   fp <- mallocForeignPtr
   withForeignPtr fp (\p -> poke p x)
   return $! fromForeignPtr (castForeignPtr fp) 0 (sizeOf x))

deserialize :: forall a . Storable a => ByteString ⊸ a
deserialize = unsafeCastLinear
 (\bs -> unsafeDupablePerformIO $ do
   let (fp,st,_) = toForeignPtr bs
       fp' :: ForeignPtr a
       fp' = castForeignPtr fp
   withForeignPtr fp' (`peekByteOff` st))

-- Cursor Types:
--------------------------------------------------------------------------------

-- | A "needs" cursor requires a list of fields be written to the
-- bytestream before the data is fully initialized.  Once it is, a
-- value of the (second) type parameter can be extracted.
newtype Needs (l :: [*]) t = Needs (Seq ByteString)

-- | A "has" cursor is a pointer to a series of consecutive,
-- serialized values.  It can be read multiple times.
newtype Has (l :: [*]) = Has (Seq ByteString)
  deriving Show

-- | A packed value is very like a singleton Has cursor.  It
-- represents a dense encoding of a single value of the type `a`.
newtype Packed a = Packed (Seq ByteString)
  deriving (Eq, NFData)

instance Show (Packed a) where
  show (Packed sq) = "Packed ["
                      ++ P.unwords (L.intersperse "|"
                         [ -- show (BS.length bs)++": "++
                           P.concat (L.intersperse "," [ show (ord c) | c <- BS.unpack bs])
                         | bs <- P.foldr (:) [] sq ]) ++ "]"


-- Cursor interface
--------------------------------------------------------------------------------

{-# INLINABLE consR #-}
consR :: Seq a ⊸ a ⊸ Seq a
consR = unsafeCastLinear2 (|>)

{-# INLINABLE writeC #-}           
-- | Write a value to the cursor.  Write doesn't need to be linear in
-- the value written, because that value is serialized and copied.
writeC :: Storable a => a -> Needs (a ': rst) t ⊸ Needs rst t
writeC a (Needs s) = Needs (s `consR` serialize a)

{-# INLINABLE readC #-}
-- | Reading from a cursor scrolls past the read item and gives a
-- cursor into the next element in the stream:
readC :: Storable a => Has (a ': rst) -> (a, Has rst)
-- One STORABLE element always constitutes one contiguous bytestring chunk:         
readC (Has (bs :<| rst)) = (deserialize bs, Has rst)
readC (Has Empty) = error "readC: impossible - read from empty cursor"

{-# INLINABLE fromHas #-}
-- | Safely "cast" a has-cursor to a packed value.
fromHas :: Has '[a] ⊸ Packed a
fromHas (Has s) = Packed s

{-# INLINABLE toHas #-}
-- | Safely cast a packed value to a has cursor.
toHas :: Packed a ⊸ Has '[a]
toHas (Packed b) = Has b

{-# INLINABLE unsafeCastNeeds #-}
-- | Perform an unsafe conversion reflecting knowledge about the
-- memory layout of a particular type (when packed).
unsafeCastNeeds :: Needs l1 a ⊸ Needs l2 a
unsafeCastNeeds (Needs b) = (Needs b)

{-# INLINABLE unsafeCastHas #-}
unsafeCastHas :: Has l1 ⊸ Has l2
unsafeCastHas (Has b) = (Has b)


{-# INLINABLE finish #-}
-- | "Cast" a fully-initialized write cursor into a read one.
finish :: Needs '[] a ⊸ Unrestricted (Has '[a])
-- We don't KNOW how many bytestring chunks the value has.  So even
-- though this may include MORE than we need, we include the whole
-- thing:
finish (Needs bss) = unsafeUnrestricted $ Has bss

{-# INLINABLE untup #-}
-- | We /could/ create a general approach to safe coercions for data
-- with the same serialized layout, analogous to, but distinct from,
-- the Coercable class.
untup :: Needs ((a,b) ': c) d ⊸ Needs (a ': b ': c) d
untup (Needs x) = Needs x

{-# INLINABLE tup #-}
tup :: Needs (a ': b ': c) d ⊸ Needs ((a,b) ': c) d
tup (Needs x) = Needs x

{-# INLINABLE withOutput #-}
-- | Allocate a fresh output cursor and compute with it.
withOutput :: forall a b. (Needs '[a] a ⊸ Unrestricted b) ⊸ Unrestricted b
withOutput fn =
    force $ fn (Needs mempty)
  where
    force :: Unrestricted b ⊸ Unrestricted b
    force (Unrestricted x) = Unrestricted x
