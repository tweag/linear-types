-- | 

module Main where
import Test.Hspec
import qualified ByteArraySpec
import qualified PackedTreeSpec


main :: IO ()
main = hspec spec

spec :: Spec
spec = do
-- Need to fix:
  describe "ByteArray" ByteArraySpec.spec
  describe "PackedTree" PackedTreeSpec.spec
