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

module Cursors
    ( Needs, Has
--    , readC, writeC
    )
    where

import Data.Monoid
import Data.Word
import Data.Int
import Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder as B
import Data.Binary (get, put, Binary, encode, decode, getWord8)
import Data.Binary.Get (runGetOrFail, Get)
import Data.Binary.Put (execPut)
import Linear.Std
import Linear.Unsafe

app :: Builder ⊸ Builder ⊸ Builder
app = unsafeCastLinear2 bapp -- HACK
 where
  bapp :: Builder -> Builder -> Builder      
  bapp = mappend

-- Cursor Types:
--------------------------------------------------------------------------------

-- | A "needs" cursor requires a list of fields be written to the
-- bytestream before the data is fully initialized.  Once it is, a
-- value of the (second) type parameter can be extracted.
newtype Needs (l :: [*]) t = Needs Builder

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
writeC :: Binary a => a -> Needs (a ': rst) t ⊸ Needs rst t
writeC a (Needs bld1) = Needs (bld1 `app` execPut (put a))

-- | Reading from a cursor scrolls past the read item and gives a
-- cursor into the next element in the stream:
readC :: Binary a => Has (a ': rst) -> (a, Has rst)
readC (Has bs) =
  case runGetOrFail get bs of
    Left (_,_,err) -> error $ "internal error: "++err
    Right (remain,num,a) -> (a, Has remain)

-- | "Cast" has-cursor to a packed value.
fromHas :: Has '[a] ⊸ Packed a
fromHas (Has b) = Packed b

toHas :: Packed a ⊸ Has '[a]
toHas (Packed b) = Has b

toBS :: Builder ⊸ ByteString
toBS = unsafeCastLinear B.toLazyByteString

-- | "Cast" a fully-initialized write cursor into a read one.
finish :: Needs '[] a ⊸ Unrestricted (Has '[a])
finish (Needs bs) = unsafeUnrestricted $ Has (toBS bs)

-- | Allocate a fresh output cursor and compute with it.
withOutput :: forall a b. (Needs '[a] a ⊸ Unrestricted b) ⊸ Unrestricted b
withOutput fn =
    force $ fn (Needs mempty)
  where
    force :: Unrestricted b ⊸ Unrestricted b
    force (Unrestricted x) = Unrestricted x

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
 deriving Show

instance Binary Tree where
      put (Leaf i)      = do put (0 :: Word8)
                             put i
      put (Branch l r) = do put (1 :: Word8)
                            put l; put r
      get = do t <- get :: Get Word8
               case t of
                    0 -> do i <- get
                            return (Leaf i)
                    1 -> do l <- get
                            r <- get
                            return (Branch l r)


caseTree :: Has (Tree ': b)
         -> (Has (Int ': b) -> a)
         -> (Has (Tree ': Tree ': b) -> a)
         -> a
caseTree (Has bs) f1 f2 =
  case runGetOrFail getWord8 bs of
    Left (_,_,err)  -> error $ "internal error: "++err
    Right (remain,num,i) ->
      case i of
        0 -> f1 (Has (BS.drop 1 bs))
        1 -> f2 (Has (BS.drop 1 bs))

-- Another Hack:
runGetLin :: ByteString ⊸ Either (ByteString,Int64,String) (ByteString,Int64,Word8)
runGetLin = unsafeCastLinear (runGetOrFail getWord8)


-- | Testing a version on a linear read cursor.
-- It should consume the first byte of its input, which could in principle
-- be freed immediately.
caseTree' :: forall b . Has (Tree ': b)
          ⊸  Either (Has (Int ': b))
                    (Has (Tree ': Tree ': b))
caseTree' = undefined
{-            
caseTree' (Has bs) = f (runGetLin bs)
  where
   f :: Either (ByteString,Int64,String) (ByteString,Int64,Word8) ⊸
        Either (Has (Int ': b)) (Has (Tree ': Tree ': b))
--   f (Left (b,n,err)) = error $ "internal error: "++err
   f (Right (remain,num,0)) = Left  (Has remain)
   f (Right (remain,num,0)) = Right (Has remain)
-}

-- | Write a complete Leaf node to the output cursor.
writeLeaf :: Int -> Needs (Tree ': b) t ⊸ Needs b t
writeLeaf n (Needs b) = 
  Needs (b `app` execPut (put (Leaf n)))

-- | Write a complete Branch node to the output cursor.
--   First, write the tag.  Second, use the provided function to
--   initialize the left and write branches.
writeBranch :: Needs (Tree ': b) t
            ⊸ (Needs (Tree ': Tree ': b) t ⊸ c)
            ⊸ c
-- writeBranch :: Needs '[Tree] t ⊸ (Needs '[Tree, Tree] t ⊸ Unrestricted b) -> b
writeBranch (Needs bs) fn =
  fn (Needs (bs `app` execPut (put (1::Word8))))


packTree :: Tree -> Packed Tree
packTree t = Packed (encode t)

unpackTree :: Packed Tree -> Tree
unpackTree (Packed t) = decode t


----------------------------------------
-- Type-safe interface below here:
----------------------------------------

-- Here we manually write functions agains the packed representation.

sumTree :: Packed Tree -> Int
sumTree pt = fin
 where
  (fin,_) = go (toHas pt)

  go :: forall b . Has (Tree ': b) -> (Int, Has b)
  go cur = caseTree cur
            (\c -> readC c)
            (\c -> let (x,c') = go c
                       (y,c'')  = go c'
                   in (x+y, c''))
           
add1 :: Packed Tree -> Packed Tree
add1 pt = fromHas fin
 where
  fin :: Has '[Tree]
  fin = getUnrestricted (withOutput f1)

  f1 :: Needs '[Tree] Tree ⊸ Unrestricted (Has '[Tree])
  f1 oc = f2 (go (toHas pt) oc)

  f2 :: (Unrestricted (Has '[]), Needs '[] Tree) ⊸ Unrestricted (Has '[Tree])
  f2 (Unrestricted _, oc2) = finish oc2

  -- This version uses ω-weight read pointers but linear write cursors.
  go :: forall b t . Has (Tree ': b) -> Needs (Tree ': b) t ⊸
                     (Unrestricted (Has b), Needs b t)
  go = undefined

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
