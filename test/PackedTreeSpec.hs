-- | 

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE CPP #-}

module PackedTreeSpec (spec) where

#if PUREMODE
#warning "Testing with PURE cursors, not internally mutable."
import Cursors.PureStorable
#else
import Cursors.Mutable
#endif
                       (withOutput, finish, Has, fromHas)
    
import PackedTree
---------------------
import Linear.Std
import Prelude hiding (($))
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

instance Arbitrary Tree where
  arbitrary = do
    stop <- frequency [(2, return True), (1, return False)]
    case stop of
      True -> Leaf <$> arbitrary
      False -> Branch <$> arbitrary <*> arbitrary

spec :: Spec 
spec = do
    describe "Cursor: write leaf" $ do
      prop "leaf written then read once" $ \ (n :: Int) -> 
        let x :: Unrestricted (Has '[Tree])
            x = withOutput (treeMaxByteSize 1)
                           (\oc -> finish (writeLeaf n oc))
        in 
        unpackTree (fromHas (getUnrestricted x)) == Leaf n

      prop "pack then unpack" $ \ (t :: Tree) ->
        t == unpackTree (packTree (treeDepth t) t)

treeDepth :: Tree -> Int
treeDepth (Leaf _) = 1
treeDepth (Branch l r) = 1 + max (treeDepth l) (treeDepth r)

