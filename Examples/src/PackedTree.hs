
-- | Use the Cursor interface to develop a tree example.

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

module PackedTree
    ( Tree(..), TagTy
    , writeLeaf
    , writeBranch
    , caseTree2
--    , caseTree, toEither
    , packTree, unpackTree
    , sumTree, mapTree
--    , foldTree, unfoldTree

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

---------------------------
-- END UNSAFE
---------------------------

--------------------------------------------------------------------------------
-- Type-safe interface below here:
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


---------------------------------------------------

-- Here we manually write functions agains the packed representation.

-- _sumTree :: Packed Tree -> Int
-- _sumTree = foldTree id (+)

-- | Optimizing away allocation.
sumTree :: Packed Tree -> Int
sumTree t = fin1
  where
    ----------- Version 5 : Raw primops, no IO ----------
{-
    (fin5,_) = go5 (toHas t)

    go5 :: Has (Tree ': r) -> (Int, Has r)
    go5 c = caseTree c readIntC onBranch

    onBranch :: forall r. Has (Tree ': Tree ': r) -> (Int, Has r)
    onBranch h1 =
      let (!x, h2) = go5 h1
          (!y, h3) = go5 h2
      in (, h3) $! x+y
-}
    ----------- Version 4 : Monadic reader with implicit read-ee state ----------
{-
    fin4 = runReadHasM (toHas t) go3 

    go4 :: ReadHasM '[Tree] Int
    go4 = caseTreeM' onLeaf onBranch

    onLeaf :: forall r. ReadHasM (Int ': r) Int
    onLeaf = withRead (\ !x -> return x)

    onBranch :: forall r. ReadHasM (Tree ': Tree ': r) Int
    -- onBranch :: ReadHasM '[Tree,Tree] Int
    onBranch = go4 `thenRead` (\ !n ->
               go4 `thenRead` (\ !m ->
               return $! n+m))
-}
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
-}
    
    ----------- Version 1 : unboxed tuples ----------
    fin1 = case withHas# (toHas t) go1 of
             (# acc, _ #) -> I# acc
                
    go1 :: forall r. Has# (Tree ': r) -> (# Int#, Has# r #)
    go1 h = caseTree2 h onLeaf onBranch

    onLeaf :: forall r. Has# (Int ': r) -> (# Int#, Has# r #)
    onLeaf h = let !(# I# n, c #) = readIntHas# h in (# n, c #)

    onBranch :: forall r. Has# (Tree ': Tree ': r) -> (# Int#, Has# r #)
    onBranch h =
      case go1 h  of { (# x, h' #) ->
      case go1 h' of { (# y, h'' #) ->
        (# x +# y,  h'' #)
      } }

{-# INLINE foldTree #-}
foldTree :: forall o. (Int -> o) -> (o -> o -> o) -> Packed Tree -> o
foldTree leaf branch tr =
    case withHas# (toHas tr) go of
      (# acc, _ #) -> acc
  where
    go :: forall r. Has# (Tree ': r) -> (# o, Has# r #)
    go h = caseTree2 h onLeaf onBranch

    onLeaf :: forall r. Has# (Int ': r) -> (# o, Has# r #)
    onLeaf h = let !(# n, c #) = readIntHas# h in (# leaf n, c #)

    onBranch :: forall r. Has# (Tree ': Tree ': r) -> (# o, Has# r #)
    onBranch h =
      let (# left,  h' #)  = go h
          (# right, h'' #) = go h'
      in (# branch left right, h'' #)

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

-- | It is safe to drop read-only Has# pointers.
dropHas :: Has# r ⊸ a ⊸ a
dropHas = unsafeCoerce (\ _ x -> x)

dropHas' :: Has# r ⊸ ()
dropHas' = unsafeCoerce (\ _ -> ())

-- | It is safe to drop numeric types.
dropNum :: Num r => r ⊸ a ⊸ a
-- dropNum :: forall r (rep :: RuntimeRep) (a :: TYPE rep) . Num r => r ⊸ a ⊸ a
dropNum = unsafeCoerce (\ _ x -> x)

{-# INLINABLE mapTree #-}
mapTree :: (Int->Int) -> Packed Tree -> Packed Tree
mapTree f pt = fromHas $ getUnrestricted fin
  where
    fin = withHas# (toHas pt) $ \h -> 
           withOutput (\n -> finishMapDest (mapDest h n))

    finishMapDest :: (# Has# '[], Needs '[] t #) ⊸ Unrestricted (Has '[t])
    finishMapDest (# h, n #) = dropHas h (finish n)

    mapDest :: Has# (Tree ': r) ⊸ Needs (Tree ': r) t ⊸ (# Has# r, Needs r t #)
    mapDest h = caseTree2 h onLeaf onBranch

    onLeaf :: forall r t . Has# (Int ': r) ->
              Needs (Tree ': r) t ⊸ (# Has# r, Needs r t #)
    onLeaf h n =
        let !(# x, h' #) = readIntHas# h in
        (# h', writeLeaf (f x) n #)

    onBranch :: forall r t . Has# (Tree ': Tree ': r) ->
                Needs (Tree ': r) t ⊸ (# Has# r, Needs r t #)
    onBranch h n = onRightBranch (mapDest h (writeBranch n))

    onRightBranch :: (# Has# (Tree ': r), Needs (Tree ': r) t #)
                   ⊸ (# Has# r, Needs r t #)
    onRightBranch (# h, n #) = mapDest h n



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
