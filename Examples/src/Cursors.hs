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

module Cursors where

import qualified ByteArray as ByteArray
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import Data.Monoid
import Data.Word
import Data.Int
import Foreign.Storable
import Linear.Std
import Prelude hiding (($))

-- Hard-coded constant:
--------------------------------------------------------------------------------
-- | Size allocated for each regions: 4KB.
regionSize :: Int
regionSize = 4096 -- in Bytes

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


-- Cursor interface
--------------------------------------------------------------------------------
         
-- | Write a value to the cursor.  Write doesn't need to be linear in
-- the value written, because that value is serialized and copied.
writeC :: Storable a => a -> Needs (a ': rst) t ⊸ Needs rst t
writeC a (Needs bld1) = Needs (ByteArray.writeStorable a bld1)

-- | Reading from a cursor scrolls past the read item and gives a
-- cursor into the next element in the stream:
readC :: Storable a => Has (a ': rst) -> (a, Has rst)
readC (Has bs) = (a, Has (ByteString.drop (sizeOf a) bs))
  where
    a = ByteArray.headStorable bs

-- | "Cast" has-cursor to a packed value.
fromHas :: Has '[a] ⊸ Packed a
fromHas (Has b) = Packed b

toHas :: Packed a ⊸ Has '[a]
toHas (Packed b) = Has b

-- | "Cast" a fully-initialized write cursor into a read one.
finish :: Needs '[] a ⊸ Unrestricted (Has '[a])
finish (Needs bs) = Has `mapU` ByteArray.freeze bs

-- | Allocate a fresh output cursor and compute with it.
withOutput :: (Needs '[a] a ⊸ Unrestricted b) ⊸ Unrestricted b
withOutput fn = ByteArray.alloc regionSize $ \ bs -> fn (Needs bs)

-- Tests:
--------------------------------------------------------------------------------

foo :: Needs '[Int, Bool] Double
foo = undefined

bar :: Needs '[Bool] Double
bar = writeC 3 foo

test01 :: Needs '[Int] a ⊸ Needs '[] a
test01 x = writeC 3 x

test02 :: Needs '[] Double
test02 = writeC True bar

test03 :: Double
test03 = fst (readC (getUnrestricted (finish test02)))

-- Example
----------------------------------------

data Tree = Leaf Int
          | Branch Tree Tree
 deriving (Show, Eq)

-- Todo?
-- instance Binary Tree where
--       put (Leaf i)      = do put (0 :: Word8)
--                              put i
--       put (Branch l r) = do put (1 :: Word8)
--                             put l; put r
--       get = do t <- get :: Get Word8
--                case t of
--                     0 -> do i <- get
--                             return (Leaf i)
--                     1 -> do l <- get
--                             r <- get
--                             return (Branch l r)


caseTree :: Has (Tree ': b)
         -> (Has (Int ': b) -> a)
         -> (Has (Tree ': Tree ': b) -> a)
         -> a
caseTree (Has bs) f1 f2 =
  case ByteString.head bs of
    0 -> f1 (Has (ByteString.drop 1 bs))
    1 -> f2 (Has (ByteString.drop 1 bs))


-- | Write a complete Leaf node to the output cursor.
writeLeaf :: Int -> Needs (Tree ': b) t ⊸ Needs b t
writeLeaf n (Needs b) = Needs (
  ByteArray.writeStorable n (ByteArray.writeByte 0 b))

-- | Write a complete Branch node to the output cursor.
--   First, write the tag.  Second, use the provided function to
--   initialize the left and write branches.
writeBranch :: Needs (Tree ': b) t ⊸ Needs (Tree ': Tree ': b) t
writeBranch (Needs bs) = Needs (ByteArray.writeByte 1 bs)


packTree :: Tree -> Packed Tree
packTree = unfoldTree viewTree
  where
    viewTree (Leaf a) = Left a
    viewTree (Branch left right) = Right (left,right)

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

unfoldTree :: forall s. (s -> Either Int (s,s)) -> s -> Packed Tree
unfoldTree step seed = fromHas $ getUnrestricted $
    withOutput (\n -> finish (go seed n))
  where
    go :: s -> Needs (Tree ': r) t ⊸ Needs r t
    go (step -> Left a) n = writeLeaf a n
    go (step -> Right (left,right)) n =
      go right (go left (writeBranch n))
           
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

{-
-- Tree tests:
----------------------------------------
        
tr1 :: Tree
tr1 = Branch (Leaf 3) (Leaf 4)

tr2 = packTree tr1
      
s1 = sumTree tr2

tr3 = unpackTree tr2

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
