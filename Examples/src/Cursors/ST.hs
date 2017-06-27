-- | A version of cursors that use ST for reading/writing.

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE StandaloneDeriving #-}

module Cursors.ST
    ( -- * Cursors
      Has, Needs, Packed
      -- * Public cursor interface
    , allocC 
    , writeC, readC
--    , readIntC
--    , fstC, rstC, fstCM, fromHas
    , toHas
    , finish
--    , withOutput, withC, withC2
-- , tup, untup
-- , hasByteSize
      
    --   -- * Utilities for unboxed usage
    -- , Has#, withHas#, unsafeCastHas#
    -- , readIntHas#, readWord8Has#
    -- , traceHas#
      
    -- * Unsafe interface
    , unsafeCastNeeds, unsafeCastHas
    -- , unsafeDropBytes

    -- * Packed Tree-specific interface
    , writeLeaf, writeBranchTag, caseTree
    )
    where

import qualified PackedTree as PT
import GHC.ST
-- import ByteArray as BA
import GHC.Types(Type)
import Foreign.Storable
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString 
import qualified Data.ByteString.Unsafe as U
import Foreign.Ptr
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.C.String (CString)
import GHC.IO (unsafeIOToST, unsafeSTToIO)
-- import GHC.Magic (runRW#)
import System.IO.Unsafe (unsafePerformIO)
--------------------------------------------------------------------------------

-- | Has cursors don't really need to be monadic:
newtype Has   s (l :: [Type])   = MkHas   ByteString    
 deriving Show
          
-- | Pure data:
newtype Packed a = MkPacked ByteString
 deriving Show

deriving instance Show (Needs s l t)

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

{-# INLINE unsafeCastNeeds #-}
unsafeCastNeeds :: Needs s l1 a -> Needs s l2 a
unsafeCastNeeds (MkNeeds i p) = (MkNeeds i p)

{-# INLINE unsafeCastHas #-}
unsafeCastHas :: Has s l1 -> Has s l2
unsafeCastHas (MkHas x) = (MkHas x)
 
{-# INLINE writeC #-}
writeC :: Storable a =>
          a -> Needs s (a ': rst) t -> ST s (Needs s rst t)

{-# INLINE allocC #-}
allocC :: Int -> ST s (Needs s '[a] a)
allocC sz = do str <- unsafeIOToST (mallocBytes sz)
               return $! MkNeeds 0 str

-- TODO: unsafeFreeze

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
finish act = unsafePerformIO $
  do MkNeeds off str <- unsafeSTToIO act
     bs <- U.unsafePackMallocCStringLen (str,off)
     return $! MkPacked bs

--------------------------------------------------------------------------------

writeLeaf :: Int -> Needs s (PT.Tree ': r) t -> ST s (Needs s r t)
writeLeaf n buf1 = do buf2 <- writeC PT.leafTag (unsafeCastNeeds buf1)
                      writeC n buf2

writeBranchTag :: Needs s (PT.Tree ': r) t
               -> ST s (Needs s (PT.Tree ': PT.Tree ': r) t)
writeBranchTag buf1 = writeC PT.branchTag (unsafeCastNeeds buf1)

caseTree :: forall s r b . Has s (PT.Tree ': r)
         -> (Has s (Int ': r)                -> ST s b)
         -> (Has s (PT.Tree ': PT.Tree ': r) -> ST s b)
         -> ST s b
caseTree h f1 f2 = do
  (tg::PT.TagTy,h') <- readC (unsafeCastHas h :: Has s '[PT.TagTy])
  case tg of
    _ | tg == PT.leafTag   -> f1 (unsafeCastHas h')
    _ | tg == PT.branchTag -> f2 (unsafeCastHas h')
