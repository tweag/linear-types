
-- | Use the Cursor interface to develop a tree example.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module PackedTree
    ( Tree(..), TagTy
    , writeLeaf
    , writeBranch
    , caseTree
    , packTree, unpackTree
    , sumTree, mapTree, foldTree, unfoldTree
    -- * Examples
    , tr1, tr2, tr3, pk0, pk1, pk2
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
import Data.Word
-- import qualified Data.ByteString as ByteString
import Prelude hiding (($))

----------------------------------------

-- | A very simple binary tree.
data Tree = Leaf !Int
          | Branch Tree Tree
 deriving (Show, Eq)

instance NFData Tree where
  rnf (Leaf n) = rnf n
  rnf (Branch x y) = rnf x `seq` rnf y

-- Unsafe bits that should be derived! 
--------------------------------------

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

{-# INLINE caseTree #-}
caseTree :: forall a b.
            Has (Tree ': b)
         -> (Has (Int ': b) -> a)
         -> (Has (Tree ': Tree ': b) -> a)
         -> a
caseTree c f1 f2 = f (readC (unsafeCastHas c))
  where   
    f :: (TagTy, Has '[]) -> a
    f (tg,c2) = case tg of
                 _ | tg == leafTag   -> f1 (unsafeCastHas c2)
                 _ | tg == branchTag -> f2 (unsafeCastHas c2)
                 _ -> error $ "caseTree: corrupt tag, "++show tg

-- | This version takes ~0.53 seconds for a tree of depth 2^20.
_packTree1 :: Tree -> Packed Tree
_packTree1 = unfoldTree viewTree
  where
    viewTree (Leaf a) = Left a
    viewTree (Branch left right) = Right (left,right)

-- | Impressively, this one goes no faster.  GHC is doing well on this
-- one.
packTree :: Tree -> Packed Tree
packTree tr0 = fromHas $ getUnrestricted $
               withOutput (\n -> finish (go tr0 n))
  where
      go :: Tree -> Needs (Tree ': r) t ⊸ Needs r t
      go (Leaf a) n = writeLeaf a n
      go (Branch left right) n =
          go right (go left (writeBranch n))

unpackTree :: Packed Tree -> Tree
unpackTree = foldTree Leaf Branch


----------------------------------------
-- Type-safe interface below here:
----------------------------------------

-- Here we manually write functions agains the packed representation.

sumTree :: Packed Tree -> Int
sumTree = foldTree id (+)

foldTree :: forall o. (Int -> o) -> (o -> o -> o) -> Packed Tree -> o
foldTree leaf branch = snd . go . toHas
  where
    go :: forall r. Has (Tree ': r) -> (Has r, o)
    go h = caseTree h onLeaf onBranch

    onLeaf :: forall r. Has (Int ': r) -> (Has r, o)
    onLeaf h = let (a, h') = readC h in (h', leaf a)

    onBranch :: forall r. Has (Tree ': Tree ': r) -> (Has r, o)
    onBranch h =
      let (h', left) = go h
          (h'', right) = go h'
      in
        (h'', branch left right)

{-# INLINABLE unfoldTree #-}
unfoldTree :: forall s. (s -> Either Int (s,s)) -> s -> Packed Tree
unfoldTree step seed = fromHas $ getUnrestricted $
    withOutput (\n -> finish (go seed n))
  where
    go :: s -> Needs (Tree ': r) t ⊸ Needs r t
    go (step -> Left a) n = writeLeaf a n
    go (step -> Right (left,right)) n =
      go right (go left (writeBranch n))
    go _ y = linerror "unfoldTree: impossible" y

{-# INLINABLE mapTree #-}
mapTree :: (Int->Int) -> Packed Tree -> Packed Tree
mapTree f pt = fromHas $ getUnrestricted $
    withOutput (\n -> finishMapDest (mapDest (toHas pt) n))
  where
    finishMapDest :: (Unrestricted (Has '[]), Needs '[] t) ⊸ Unrestricted (Has '[t])
    finishMapDest (Unrestricted _, n) = finish n

    mapDest :: Has(Tree ': r) -> Needs(Tree ': r) t ⊸ (Unrestricted (Has r), Needs r t)
    mapDest h = caseTree h onLeaf onBranch

    onBranch :: Has (Tree ': Tree ': r) -> Needs (Tree ': r) t ⊸ (Unrestricted (Has r), Needs r t)
    onBranch h n = onRightBranch (mapDest h (writeBranch n))

    onRightBranch :: (Unrestricted (Has (Tree ': r)), Needs (Tree ': r) t) ⊸ (Unrestricted (Has r), Needs r t)
    onRightBranch (Unrestricted h, n) = mapDest h n

    onLeaf :: Has (Int ': r) -> Needs (Tree ': r) t ⊸ (Unrestricted (Has r), Needs r t)
    onLeaf h n =
      let (a, h') = readC h
      in
        (Unrestricted h', writeLeaf (f a) n)

  -- This version uses linear read and write cursors.
{- 
  -- Polymorphic version that works with anything following the Tree in the buffer.
  go :: forall b t . Has (Tree ': b) ⊸ Needs (Tree ': b) t ⊸
                     (Has b ⊗ Needs b t)
  go inC outC =
       case caseTree' inC of
         Left  c2 -> let (n,c3) = readC c2 in
                     Tensor c3 (writeLeaf (n+1) outC)
         Right c2 ->           
            writeBranch outC (\oc2 ->
              let Tensor c3 oc3 = go c2 oc2
                  Tensor c4 oc4 = go c3 oc3 -- Bug? c4 etc should be weight 1
              in Tensor c4 oc4)
-}

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
      
tr2 :: Packed Tree
tr2 = packTree tr1

tr3 :: Tree
tr3 = unpackTree tr2

{-
      
s1 = sumTree tr2



tr4 :: Packed Tree
tr4 = fromHas $
      withOutput (\c -> Unrestricted (finish (writeLeaf 33 c)))

tr5 = unpackTree tr4

tr6 :: Packed Tree
tr6 = fromHas $
      withOutput $ \c -> Unrestricted $ 
       writeBranch c (\c2 ->
            let c3 = writeLeaf 33 c2
                c4 = writeLeaf 44 c3
            in finish c4)

s2 = sumTree tr6
     
tr7 = unpackTree tr6

tr8 = add1 tr6

tr9 = unpackTree tr8      

-}
