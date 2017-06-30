module PurifySpec where

import Purify
---------------------
import Linear.Std
import Prelude hiding (($))
import Test.Hspec
import Test.Hspec.QuickCheck (prop)

leaf :: IO (MTree Int)
leaf = newTree VLeaf

node :: Int -> IO (MTree Int) -> IO (MTree Int) -> IO (MTree Int)
node a m1 m2 = do
  m1' <- m1
  m2' <- m2
  newTree (VNode m1' a m2')

createMTree :: IO (MTree Int)
createMTree = do
  node 2 (node 3 (node 1 leaf leaf) leaf) (node 5 leaf leaf)

three :: MTree Int -> IO Int
three mtree = do
  VNode left _ _ <- readTree mtree
  VNode _ r _ <- readTree left
  return r

one :: MTree Int -> IO Int
one mtree = do
  VNode left _  _ <- readTree mtree
  VNode lleft _ _ <- readTree left
  VNode _ r _ <- readTree lleft
  return r

spec :: Spec
spec = do
    describe "Test functions" $ do
      it "pass a sanity check" $ do
        t <- createMTree
        three_ <- three t
        one_ <- one t
        three_ `shouldBe` 3
        one_ `shouldBe` 1

    describe "MapTree" $ do
      it "reads-back correctly" $ do
        t <- createMTree
        t' <- updateTree t (mapTree (+1))
        three_ <- three t'
        one_ <- one t'
        three_ `shouldBe` 4
        one_ `shouldBe` 2

    describe "Composition" $ do
      it "commutes with update" $ do
        t1 <- createMTree
        t2 <- createMTree
        let f1 = mapTree (+1)
        let f2 = mapTree (*2)
        t1' <- updateTree t1 (f2 . f1)
        t2' <- flip updateTree f2 =<< updateTree t2 f1
        one1 <- one t1'
        one2 <- one t2'
        three1 <- three t1'
        three2 <- three t2'
        one1 `shouldBe` one2
        three1 `shouldBe` three2
