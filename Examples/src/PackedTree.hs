
-- | Use the Cursor interface to develop a tree example.

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

module PackedTree
    ( Tree(..), TagTy
    , writeLeaf
    , writeBranch
    , caseTree, toEither
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
import ByteArray (runReadM, ReadM, headStorableM)
import Foreign.Storable
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


{-# INLINE caseTree2 #-}
caseTree2 :: forall a1 a2 b.
             Has (Tree ': b)
          -> (Has (Int ': b) -> (# a1, a2 #))
          -> (Has (Tree ': Tree ': b) -> (# a1, a2 #))
          -> (# a1, a2 #)
caseTree2 c f1 f2 = f (fstC c2)
  where 
    c2 = unsafeCastHas c 
    f tg | tg == leafTag   = f1 (unsafeCastHas (rstC c2))
         | tg == branchTag = f2 (unsafeCastHas (rstC c2))
--                 _ -> error $ "caseTree2: corrupt tag, "++show tg

type EitherTree b = Either (Has (Int ': b)) (Has (Tree ': Tree ': b))

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

--------------------------------------------------------------------------------
-- A more strongly-typed bytestream-reader monad:
--------------------------------------------------------------------------------

newtype ReadHasM (a :: [*]) b = ReadHasM (ReadM b)
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
    let (ReadHasM a) = fn x
    a

-- | Run a computation that reads part of the stream, then run
-- something else after it to consume the rest.
thenRead :: ReadHasM '[a] b -> (b -> ReadHasM r c) -> ReadHasM (a ': r) c
thenRead (ReadHasM m) fn = ReadHasM $ 
         do x <- m
            let (ReadHasM m2) = fn x
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
    
--------------------------------------------------------------------------------
             
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

_sumTree :: Packed Tree -> Int
_sumTree = foldTree id (+)

-- | Optimizing away allocation.
sumTree :: Packed Tree -> Int
sumTree t = fin3
  where
    ----------- Version 4 : Monadic reader with implicit read-ee state ----------
    fin3 = runReadHasM (toHas t) go3 

    go3 :: ReadHasM '[Tree] Int
    go3 = caseTreeM' onLeaf onBranch

    onLeaf :: forall r. ReadHasM (Int ': r) Int
    onLeaf = withRead return

    onBranch :: forall r. ReadHasM (Tree ': Tree ': r) Int
    -- onBranch :: ReadHasM '[Tree,Tree] Int
    onBranch = go3 `thenRead` (\ !n ->
               go3 `thenRead` (\ !m ->
               return $! n+m))

    ----------- Version 3 : Monadic reader, change scope of runRW# ----------
{-    
    fin3 = fst $ runReadM $ go3 (toHas t)

    go3 :: forall r. Has (Tree ': r) -> ReadM (Int, Has r)
    go3 h = caseTreeM h onLeaf onBranch

    onLeaf :: forall r. Has (Int ': r) -> ReadM (Int, Has r)
    onLeaf h = do !n <- fstCM h
                  return (n, rstC h)

    onBranch :: forall r. Has (Tree ': Tree ': r) -> ReadM (Int, Has r)
    onBranch h1 = do
      (n,h2) <- go3 h1
      (m,h3) <- go3 h2
      return (n+m, h3)
-}
{-
    ----------- Version 2 : Either ----------
    fin2 = go (toHas t) fst

    go :: forall a r. Has (Tree ': r) -> ((Int, Has r) -> a) -> a
    go h k = withEither h
             (\e ->
               case e of
                 Left h1  -> withC h1 (\n -> k (n, rstC h1))
                 Right h1 -> go h1 (\(n,h2) -> go h2 (\(m,h3) -> k (n+m,h3)))
             )
    
    ----------- Version 1 : unboxed tuples ----------
    fin1 = case go1 (toHas t) of
             (# acc, _ #) -> acc
    
    go1 :: forall r. Has (Tree ': r) -> (# Int, Has r #)
    go1 h = caseTree2 h onLeaf onBranch

    onLeaf :: forall r. Has (Int ': r) -> (# Int, Has r #)
    onLeaf h = let (n, c) = readC h in (# n, c #)

    onBranch :: forall r. Has (Tree ': Tree ': r) -> (# Int, Has r #)
    onBranch h =
      case go1 h  of { (# x, h' #) ->
      case go1 h' of { (# y, h'' #) ->
        (# x+y,  h'' #)
      } }
-}

{-# INLINABLE foldTree #-}
foldTree :: forall o. (Int -> o) -> (o -> o -> o) -> Packed Tree -> o
foldTree leaf branch = snd . go . toHas
  where
    go :: forall r. Has (Tree ': r) -> (Has r, o)
    go h = caseTree h onLeaf onBranch

    onLeaf :: forall r. Has (Int ': r) -> (Has r, o)
    onLeaf h = let (a, h') = readC h in (h', leaf a)

    onBranch :: forall r. Has (Tree ': Tree ': r) -> (Has r, o)
    onBranch h =
      let (h', left)   = go h
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
