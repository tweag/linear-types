
-- | An interface for mutable byte arrays, handled linearly.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE NamedFieldPuns #-}

module ByteArray
    ( WByteArray, alloc, freeze, headStorable, writeStorable, writeByte )
    where

import Data.ByteString (ByteString)
-- import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Unsafe as ByteString (unsafePackMallocCStringLen, unsafeUseAsCString)
import Data.Word
import Foreign.C.String
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr
import Foreign.Storable
import Foreign.C.Types
import Linear.Std
import Linear.Unsafe
import Prelude hiding (rem,($))
import System.IO.Unsafe (unsafePerformIO, unsafeDupablePerformIO)

-- import GHC.IO
-- import GHC.Prim (RealWorld, State#)
---------------------------------

-- type Token = State# RealWorld

data WByteArray = WBA { pos :: !CString
                      , orig :: !CString
--                      , stored :: !Int
--                      , rem :: !Int
--                      , state :: Token
                      }

{-# NOINLINE alloc #-}
-- | Allocate and use a mutable, linear byte array.
alloc :: Int -> (WByteArray ⊸ Unrestricted b) ⊸ Unrestricted b
alloc i f = forceUnrestricted $ f $ unsafePerformIO $ do
     str <- mallocBytes (i+1) -- Remark: can't use @alloca@ as the pointer will usually survive the scope
     pokeElemOff str i (0::CChar) -- Null terminated.
     return $! WBA{ pos = str
                  , orig = str
--                  , stored = 0
--                  , rem = i
                  }
-- Todo: @alloc@ should handle exception and free the pointer it allocates.


{-# INLINE writeByte #-}
-- | Write a single byte to the end of a byte array.
writeByte :: Word8 -> WByteArray ⊸ WByteArray
writeByte = writeStorable

{-# INLINE writeStorable #-}
-- | Write a storable value to the end of a byte array.
writeStorable :: Storable a => a -> WByteArray ⊸ WByteArray
writeStorable obj wbarr = write (unsafeUnrestricted wbarr)
  where
    write :: Unrestricted WByteArray ⊸ WByteArray
    write (Unrestricted WBA{pos,orig}) =       
      let !_         = unsafeDupablePerformIO (poke (castPtr pos) obj)
          size       = sizeOf obj
          newPos     = pos `plusPtr` size -- no alignment 
--          sizeStored = newPos `minusPtr` pos wba
      in
      WBA { pos    = newPos
          , orig   = orig
--          , stored = stored wba + sizeStored
--          , rem = rem wba - sizeStored,
          }

{-# NOINLINE freeze #-}
freeze :: WByteArray ⊸ Unrestricted ByteString
freeze wba =
    pack (project (unsafeUnrestricted wba))
  where
    project :: Unrestricted WByteArray ⊸ Unrestricted CStringLen
    project (Unrestricted (WBA{orig, pos})) = Unrestricted (orig,pos `minusPtr` orig)

    pack :: Unrestricted CStringLen ⊸ Unrestricted ByteString
    pack (Unrestricted cstr) = Unrestricted $ unsafePerformIO $
        ByteString.unsafePackMallocCStringLen cstr

{-# INLINE headStorable #-}
-- TODO: bound checking
headStorable :: Storable a => ByteString -> a
headStorable bs = unsafeDupablePerformIO $
    ByteString.unsafeUseAsCString bs $ \ cstr ->
      peek (castPtr cstr)
