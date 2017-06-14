-- | Cursors into byte-addressed memory that allow type-safe writing
-- and reading of serialized data.
-- 
-- Requires the "linear-types" branch of GHC from the tweag.io fork.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Examples.Cursors
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

-- Prereqs
--------------------------------------------------------------------------------

data a ⊗ b where
 Tensor :: a ⊸ b ⊸ a ⊗ b
  deriving Show

-- Fails, as it should:
-- flip' :: a ⊗ a ⊸ a ⊗ a
-- flip' (Tensor a b) = Tensor b b
 
flipT :: a ⊗ b ⊸ b ⊗ a
flipT (Tensor a b) = Tensor b a

--------------------------------------------------------------------------------

data Unrestricted a = Unrestricted a
  deriving (Show,Eq)
                    
-- unrTest :: Unrestricted a -> (Unrestricted a, Unrestricted a)
-- unrTest (Unrestricted x) = (Unrestricted x, Unrestricted x)
-- unrTest x = (x, x)

f :: Int ⊸ Unrestricted Int
f n = Unrestricted n

g :: Int ⊸ Int
g n = n
 -- No linear let atm:
 -- let _ = n in 3
 -- This won't work:
 -- (\_ -> 3) n
--   case n of _ -> 3

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
{-                    
--------------------------------------------------------------------------------
                    
-- write :: Needs (a ': b) t ⊸ a -> Needs b t
-- write (Needs bs) a = case bs of _ -> undefined

-- write :: a ⊸ Needs (a ': b) t ⊸ Needs b t
-- | Write a value to the cursor.  Write doesn't need to be linear in
-- the value written, because that value is serialized and copied.
writeC :: Binary a => a -> Needs (a ': rst) t ⊸ Needs rst t
writeC a nds =
  case nds of
    Needs bld1 -> Needs (bld1 `mappend`
                         execPut (put a))

-- unsafeCoerceNeeds :: Needs a t -> Needs b t
                  
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

         
-- | "Cast" a fully-initialized write cursor into a read one.
finish :: Needs '[] a ⊸ Has '[a]
finish (Needs bs) = Has (toBS bs)

toBS :: Builder ⊸ ByteString
toBS = B.toLazyByteString -- Why is this allowed?  Bug?
-- toBS x = B.toLazyByteString x -- This isn't.

-- | Allocate a fresh output cursor and compute with it.
withOutput :: (Needs '[a] a ⊸ Unrestricted b) -> b
withOutput fn =
  case fn (Needs mempty) of
    Unrestricted x -> x

-- Tests:
--------------------------------------------------------------------------------

-- foo :: Needs '[Int, Bool] Double
-- foo = undefined

-- bar :: Needs '[Bool] Double
-- bar = write foo 3

-- test :: Needs '[Int] a ⊸ Needs '[] a
-- test x = let y = write 3 x in case y of _ -> y

-- test2 :: Int ⊸ Int
-- test2 x = case x of _ -> x


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


caseTree' :: Has (Tree ': b)
          ⊸  Either (Has (Int ': b))
                    (Has (Tree ': Tree ': b))
caseTree' (Has bs) = 
  case runGetLin bs of
    Left (_,_,err)  -> error $ "internal error: "++err
    Right (remain,num,i) ->
      case i of
        0 -> Left  (Has remain)
        1 -> Right (Has remain)

-- Another Hack:
runGetLin :: ByteString ⊸ Either (ByteString,Int64,String) (ByteString,Int64,Word8)
runGetLin = runGetOrFail getWord8

-- | Write a complete Leaf node to the output cursor.
writeLeaf :: Int -> Needs (Tree ': b) t ⊸ Needs b t
writeLeaf n (Needs b) = 
  Needs (b `app` execPut (put (Leaf n)))

app :: Builder ⊸ Builder ⊸ Builder
app = mappend -- HACK

-- | Write a complete Branch node to the output cursor.
--   First, write the tag.  Second, use the provided function to
--   initialize the left and write branches.
writeBranch :: Needs (Tree ': b) t
            ⊸ (Needs (Tree ': Tree ': b) t ⊸ c)
            ⊸ c
-- writeBranch :: Needs '[Tree] t ⊸ (Needs '[Tree, Tree] t ⊸ Unrestricted b) -> b
writeBranch (Needs bs) fn =
  let n2 = Needs (bs `app` execPut (put (1::Word8))) in  
  fn n2
--  case fn n2 of Unrestricted b -> b

packTree :: Tree -> Packed Tree
packTree t = Packed (encode t)

unpackTree :: Packed Tree -> Tree
unpackTree (Packed t) = decode t

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
  fin = withOutput (\oc ->
                    let Tensor c oc2 = go (toHas pt) oc in
                    case c of
                      _ -> Unrestricted (finish oc2))

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
