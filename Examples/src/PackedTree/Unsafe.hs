-- | The internals of the packed tree representation.

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module PackedTree.Unsafe 
    ( Tree(..), TagTy
    , writeLeaf
    , writeBranch
    , caseTree2
--    , caseTree, toEither

    , dropHas
--    , dropNum

    -- * Examples
    , tr1, pk0, pk1, pk2
    ) where

#ifdef PUREMODE
#warning "Building library with PURE cursors, not internally mutable."
import Cursors.PureStorable
#else
#warning "Building library with internally MUTABLE cursors."
import Cursors.Mutable
#endif

import Control.DeepSeq
import Linear.Std
-- import Linear.Unsafe (unsafeCastLinear)
import Unsafe.Coerce (unsafeCoerce)
import Data.Word
-- import qualified Data.ByteString as ByteString
import Prelude hiding (($))
import ByteArray (runReadM, ReadM, headStorableM, headWord8')
import Foreign.Storable
import GHC.Prim(ord#, Int#, (+#), TYPE)
import GHC.Int(Int(..))
import GHC.Types(RuntimeRep, Type)
import Debug.Trace (trace)
      
----------------------------------------

-- | A very simple binary tree.
data Tree = Leaf !Int
          | Branch Tree Tree
 deriving (Show, Eq)

instance NFData Tree where
  rnf (Leaf n) = rnf n
  rnf (Branch x y) = rnf x `seq` rnf y

--------------------------------------------------------------------------------
-- UNSAFE bits that should be derived! 
--------------------------------------------------------------------------------

type TagTy = Word8

leafTag   :: TagTy; leafTag   = 100
branchTag :: TagTy; branchTag = 111

{-# INLINE writeLeaf #-}
-- | Write a complete Leaf node to the output cursor.
writeLeaf :: Int -> Needs (Tree ': b) t ⊸ Needs b t
writeLeaf n oc = writeLeaf' n (unsafeCastNeeds oc)
  where
   writeLeaf' :: Int -> Needs (TagTy ': Int ': b) t ⊸ Needs b t
   writeLeaf' x c = writeC x (writeC leafTag c)

{-# INLINE writeBranch #-}
-- | Write a complete Branch node to the output cursor.
--   First, write the tag.  Second, use the provided function to
--   initialize the left and write branches.
writeBranch :: forall b t . Needs (Tree ': b) t ⊸ Needs (Tree ': Tree ': b) t
writeBranch oc = writeC branchTag (unsafeCastNeeds oc)

-- Todo?
-- instance Binary Tree where
--       put (Leaf i)      = do put (0 :: TagTy)
--                              put i
--       put (Branch l r) = do put (1 :: TagTy)
--                             put l; put r
--       get = do t <- get :: Get TagTy
--                case t of
--                     0 -> do i <- get
--                             return (Leaf i)
--                     1 -> do l <- get
--                             r <- get
--                             return (Branch l r)

#ifndef PUREMODE
{-# INLINE caseTree #-}
caseTree :: forall a b.
            Has (Tree ': b)
         -> (Has (Int ': b) -> a)
         -> (Has (Tree ': Tree ': b) -> a)
         -> a
caseTree c@(Has bs) f1 f2 =
    case ord# (headWord8' bs) of
      100# -> f1 (unsafeDropBytes 1 c)
      _    -> f2 (unsafeDropBytes 1 c)
#endif

{-# INLINE caseTree2 #-}
caseTree2 :: forall (rep :: RuntimeRep) (res :: TYPE rep) b.
             Has# (Tree ': b)
          ⊸  (Has# (Int ': b) ⊸ res )
          -> (Has# (Tree ': Tree ': b) ⊸ res )
          -> res
caseTree2 h f1 f2 =    
    (f (readWord8Has# (unsafeCastHas#
         -- (traceHas# "caseTree2 on " h)
         h
         )))
 where
   f :: (# Word8, Has# '[] #) ⊸ res
   f (# 100 , c2 #) = f1 (unsafeCastHas# c2)
   f (# 111 , c2 #) = f2 (unsafeCastHas# c2)
   f (# x, c2 #) =       
       ((error "impossible: got an invalid tag")
            :: Word8 ⊸ Has# '[] ⊸ res) x c2


type EitherTree b = Either (Has (Int ': b)) (Has (Tree ': Tree ': b))

#ifndef PUREMODE
{-# INLINE toEither #-}
toEither :: forall b. Has (Tree ': b) -> EitherTree b
toEither c =
    let 
        c2 = unsafeCastHas c in
    case fstC c2 of 
      tg | tg == leafTag   -> Left  (rstC (unsafeCastHas c2:: Has (TagTy ': Int ': b)))
         | tg == branchTag -> Right (rstC (unsafeCastHas c2:: Has (TagTy ': Tree ': Tree ': b)))
         | otherwise -> error $ "toEither: corrupt tag, "++show tg


{-# INLINE withEither #-}
withEither :: forall a b. Has (Tree ': b) -> (EitherTree b -> a) -> a
withEither c f = withC c2 f2
  where
   c2 = unsafeCastHas c
   f2 tg | tg == leafTag   = f (Left  (rstC (unsafeCastHas c2:: Has (TagTy ': Int ': b))))
         | tg == branchTag = f (Right (rstC (unsafeCastHas c2:: Has (TagTy ': Tree ': Tree ': b))))
         | otherwise = error $ "withEither: corrupt tag, "++show tg


-- toEitherM :: forall b. Has (Tree ': b) -> ReadM (EitherTree b)

{-# INLINE caseTreeM #-}
caseTreeM :: forall a b.
            Has (Tree ': b)
         -> (Has (Int ': b) -> ReadM a)
         -> (Has (Tree ': Tree ': b) -> ReadM a)
         -> ReadM a
caseTreeM c f1 f2 =
    do let c2 = unsafeCastHas c
       tg::TagTy <- fstCM c2
       if tg == leafTag
        then f1 (unsafeCastHas (rstC c2))
        else f2 (unsafeCastHas (rstC c2))
#endif
             
--------------------------------------------------------------------------------
-- A bytestream-reader monad:
--------------------------------------------------------------------------------

#ifndef PUREMODE
newtype ReadHasM (a :: [Type]) b = ReadHasM (ReadM b)
  deriving (Functor, Applicative, Monad)

-- | Run a reader computation with the input bytestream.  However, this
-- bytestream is not reclaimable memory until the computation has completely finished.
runReadHasM :: Has '[a] -> ReadHasM '[a] b -> b
runReadHasM (Has b) (ReadHasM rm) = runReadM b rm 

-- | Read a single value off the implicit stream, and continue to
-- compute using that value.
withRead :: Storable a => (a -> ReadHasM r b) -> ReadHasM (a ': r) b 
withRead fn = ReadHasM $ do 
    x <- headStorableM
    let (ReadHasM a) = fn $! x
    a

-- | Run a computation that reads part of the stream, then run
-- something else after it to consume the rest.
thenRead :: ReadHasM '[a] b -> (b -> ReadHasM r c) -> ReadHasM (a ': r) c
thenRead (ReadHasM m) fn = ReadHasM $ 
         do x <- m
            let (ReadHasM m2) = fn $! x
            m2
    
-- | Read a tree value directly from the implicit reader state.
caseTreeM' :: ReadHasM (Int ': r) b
           -> ReadHasM (Tree ': Tree ': r) b
           -> ReadHasM (Tree ': r) b
caseTreeM' (ReadHasM m1) (ReadHasM m2) = ReadHasM $ do
  (tg::TagTy) <- headStorableM
  if tg == leafTag
    then m1
    else m2
#endif


-- DROP 
---------------------------

-- | It is safe to drop read-only Has# pointers.
dropHas :: Has# r ⊸ a ⊸ a
dropHas = unsafeCoerce (\ _ x -> x)

dropHas' :: Has# r ⊸ ()
dropHas' = unsafeCoerce (\ _ -> ())

-- | It is safe to drop numeric types.
dropNum :: Num r => r ⊸ a ⊸ a
-- dropNum :: forall r (rep :: RuntimeRep) (a :: TYPE rep) . Num r => r ⊸ a ⊸ a
dropNum = unsafeCoerce (\ _ x -> x)



-- Tree tests:
----------------------------------------
        
tr1 :: Tree
tr1 = Branch (Leaf 3) (Leaf 4)

pk0 :: Packed TagTy
pk0 = fromHas $ getUnrestricted $
      withOutput (\c -> finish (writeC leafTag c))

pk1 :: Packed (TagTy, TagTy)
pk1 = fromHas $ getUnrestricted $
      withOutput (\(c :: Needs '[(TagTy,TagTy)] (TagTy,TagTy)) ->
                      finish (writeC leafTag (writeC leafTag (untup c))))

pk2 :: Packed Tree
pk2 = fromHas $ getUnrestricted $
      withOutput (\c -> finish (writeLeaf 33 c))
      

