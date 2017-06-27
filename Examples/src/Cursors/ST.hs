-- | A version of cursors that use ST for reading/writing.

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}

module Cursors.ST
    ( -- * Cursors
      Has, Needs, Packed
      -- * Public cursor interface
    , writeC, readC
--    , readIntC
--    , fstC, rstC, fstCM, fromHas, toHas
    , finish
--    , withOutput, withC, withC2
-- , tup, untup
-- , hasByteSize
      
    --   -- * Utilities for unboxed usage
    -- , Has#, withHas#, unsafeCastHas#
    -- , readIntHas#, readWord8Has#
    -- , traceHas#
      
    --   -- * Unsafe interface
    -- , unsafeCastNeeds, unsafeCastHas
    -- , unsafeDropBytes
    )
    where

import GHC.ST
import ByteArray as BA
import GHC.Types(RuntimeRep, Type)
import Foreign.Storable
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString 
import qualified Data.ByteString.Unsafe as U
import Foreign.Ptr
import Foreign.C.String (CString)
import Foreign.Storable
import GHC.IO (unsafeIOToST)
--------------------------------------------------------------------------------

-- | Has cursors don't really need to be monadic:
newtype Has   s (l :: [Type])   = MkHas   ByteString    

-- | Pure data:
newtype Packed a = MkPacked ByteString

#if 0
-- | Needs-cursors must be monadic.
newtype Needs s (l :: [Type]) t = MkNeeds BA.WByteArray
 
-- | UNSAFE!  Must be used linearly.
writeC a (MkNeeds wba) = do
  unsafeIOToST $ BA.writeStorableIO a wba
  return (MkNeeds wba)

#else
data Needs s (l :: [Type]) t = MkNeeds !Int !CString
-- | This version is safer, in the sense that non-linearity will
-- result in overwriting data but will NOT corrupt the Needs cursor
-- itself.
writeC a (MkNeeds off str) = do
  unsafeIOToST $ poke (castPtr str `plusPtr` off) a
  return $! MkNeeds (off+sizeOf a) str
#endif

{-# INLINE writeC #-}
writeC :: Storable a =>
          a -> Needs s (a ': rst) t -> ST s (Needs s rst t)


{-# INLINE readC #-}
readC :: forall a s rst . Storable a =>
         Has s (a ': rst) -> ST s (a, Has s rst)
readC (MkHas bs) = unsafeIOToST $ do
  x <- U.unsafeUseAsCString bs $ \ cstr -> 
         peek (castPtr cstr)
  return (x, MkHas (ByteString.drop (sizeOf(undefined::a)) bs))

{-# INLINE toHas #-}
toHas :: Packed a -> Has s '[a]
toHas (MkPacked b) = MkHas b
         
-- | Run the computation to completion and freeze the result.
--   It becomes immutable to subsequent consumers.
{-# INLINE finish #-}
finish :: (forall s . ST s (Needs s '[] t)) -> Packed t
finish (ST fn)  =
    undefined
--    BA.freeze bs
