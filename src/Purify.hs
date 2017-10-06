{-# LANGUAGE LambdaCase #-}

module Purify where

import Data.IORef
import Linear.Std
import Prelude hiding (($))

-- * Input: impure API
--
-- The impure API is straightforward: trees an be written or read. This is
-- expressed in as tyle reminiscent of a free algebra of a functor because it
-- yields a very small of expressive primitives.

data MTree a = MTree (IORef (TreeView a))

data TreeView a = VLeaf | VNode (MTree a) a (MTree a)

readTree :: MTree a -> IO (TreeView a)
readTree (MTree mtree) = readIORef mtree

writeTree :: MTree a -> TreeView a -> IO ()
writeTree (MTree mtree) = writeIORef mtree

newTree :: TreeView a -> IO (MTree a)
newTree view = MTree <$> newIORef view

-- * Output: pure API

-- | Pure trees. A normal binary-tree data-type, except for the possible
-- references to a mutable tree in both 'Node' and 'Leaf. This reference, is
-- crucial: it gives a correspondance between the pure tree representation of
-- the state, and the state itself. When we write back a pure tree into the
-- state, if there is such a reference, we update the corresponding state node
-- rather than creating an entirely new node.
data Tree a
  = Leaf (Maybe (MTree a))
  | Node (Tree a) (Unrestricted a) (Tree a) (Maybe (MTree a))

-- | 'mapTree' is not an API function: 'Tree' is a transparent data-type, so
-- 'mapTree' is definable. It is important that 'mapTree' is linear, since we
-- want to use it with 'updateTree', where we need a linear function.
mapTree :: (a -> a) -> Tree a ⊸ Tree a
mapTree _ (Leaf mmtree) = Leaf mmtree
mapTree f (Node left (Unrestricted x) right mmtree) =
    Node (mapTree f left) (Unrestricted (f x)) (mapTree f right) mmtree

-- | The safe update function is a thin wrapper around internal functions
-- below. Note that 'updateTree' would have typechecked if we passed an
-- unrestricted @Tree a -> Tree a@ function, but it wouldn't be a safe function
-- then. Unsafety, for the purpose of this module, is characterised by the fact
-- that if a reference to an 'MTree' occurs twice in the resulting 'Tree', the
-- result will be non-sensic.
updateTree :: MTree a -> (Tree a ⊸ Tree a) -> IO (MTree a)
updateTree mtree upd = do
  tree <- unmarshallMTree mtree
  unsafeUpdateTree tree (upd tree)

-- * Unsafe internals

-- | Simple but useful wrapper: tries to update an 'MTree', but allocates a new
-- 'MTree' instead if 'Nothing' is passed.
maybeWriteTree :: Maybe (MTree a) -> TreeView a -> IO (MTree a)
maybeWriteTree (Just mtree) v = writeTree mtree v >> return mtree
maybeWriteTree Nothing v = newTree v

-- | Update an 'MTree' based on the difference between the two 'Tree' arguments
-- so that the returned 'MTree' reflects the second 'Tree' argument. Assumes
-- that the references on the second 'Tree' are not repeated.
unsafeUpdateTree :: Tree a -> Tree a -> IO (MTree a)
unsafeUpdateTree (Node l1 _ r1 _) (Node l2 (Unrestricted a2) r2 mmtree) = do
  ml2 <- unsafeUpdateTree l1 l2
  mr2 <- unsafeUpdateTree r1 r2
  mtree <- maybeWriteTree mmtree (VNode ml2 a2 mr2)
  return mtree
unsafeUpdateTree _ tree = unsafeAllocTree tree

-- | Handles writing back a 'Tree' for 'unsafeUpdateTree' for cases besides
-- Node/Node: there is nothing to compare the subtrees with.
unsafeAllocTree :: Tree a -> IO (MTree a)
unsafeAllocTree (Leaf mmtree) = do
  mtree <- maybeWriteTree mmtree VLeaf
  return mtree
unsafeAllocTree (Node l (Unrestricted a) r mmtree) = do
  ml <- unsafeAllocTree l
  mr <- unsafeAllocTree r
  mtree <- maybeWriteTree mmtree (VNode ml a mr)
  return mtree

-- | Creates a view from a state. For each node, recalls its origin mutable
-- node.
unmarshallMTree :: MTree a -> IO (Tree a)
unmarshallMTree mtree =
  readTree mtree >>= \case
    VLeaf -> return $ Leaf (Just mtree)
    VNode ml a mr -> do
      l <- unmarshallMTree ml
      r <- unmarshallMTree mr
      return $ Node l (Unrestricted a) r (Just mtree)
