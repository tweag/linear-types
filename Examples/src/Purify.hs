{-# LANGUAGE LambdaCase #-}

module Purify where

import Linear.Std
import Prelude hiding (($))

-- Input: impure API
data MTree a = MTree -- TODO

data TreeView a = VLeaf | VNode (MTree a) a (MTree a)
readTree :: MTree a -> IO (TreeView a)
readTree = error "TODO: readTree"

writeTree :: MTree a -> TreeView a -> IO ()
writeTree = error "TODO: writeTree"

newTree :: TreeView a -> IO (MTree a)
newTree = error "TODO: newTree"

-- Output: pure API
data Tree a
  = Leaf (Maybe (MTree a))
  | Node (Tree a) (Unrestricted a) (Tree a) (Maybe (MTree a))

mapTree :: (a -> a) -> Tree a ⊸ Tree a
mapTree _ (Leaf mmtree) = Leaf mmtree
mapTree f (Node left (Unrestricted x) right mmtree) =
    Node (mapTree f left) (Unrestricted (f x)) (mapTree f right) mmtree

maybeWriteTree :: Maybe (MTree a) -> TreeView a -> IO (MTree a)
maybeWriteTree (Just mtree) v = writeTree mtree v >> return mtree
maybeWriteTree Nothing v = newTree v

unsafeUpdateTree :: Tree a -> Tree a -> IO (MTree a)
unsafeUpdateTree (Node l1 _ r1 _) (Node l2 (Unrestricted a2) r2 mmtree) = do
  ml2 <- unsafeUpdateTree l1 l2
  mr2 <- unsafeUpdateTree r1 r2
  mtree <- maybeWriteTree mmtree (VNode ml2 a2 mr2)
  return mtree
unsafeUpdateTree _ tree = unsafeAllocTree tree

unsafeAllocTree :: Tree a -> IO (MTree a)
unsafeAllocTree (Leaf mmtree) = do
  mtree <- maybeWriteTree mmtree VLeaf
  return mtree
unsafeAllocTree (Node l (Unrestricted a) r mmtree) = do
  ml <- unsafeAllocTree l
  mr <- unsafeAllocTree r
  mtree <- maybeWriteTree mmtree (VNode ml a mr)
  return mtree

unmarshallMTree :: MTree a -> IO (Tree a)
unmarshallMTree mtree =
  readTree mtree >>= \case
    VLeaf -> return $ Leaf (Just mtree)
    VNode ml a mr -> do
      l <- unmarshallMTree ml
      r <- unmarshallMTree mr
      return $ Node l (Unrestricted a) r (Just mtree)

updateTree :: MTree a -> (Tree a ⊸ Tree a) -> IO (MTree a)
updateTree mtree upd = do
  tree <- unmarshallMTree mtree
  unsafeUpdateTree tree (upd tree)
