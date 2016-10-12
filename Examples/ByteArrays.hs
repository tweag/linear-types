{-# LANGUAGE TypeOperators, GADTs #-}
module ByteArrays where

import Foreign
import Foreign.Marshal.Array
import Foreign.C
import System.IO.Unsafe


-- Broken man's linear types.
type a ⊗ b = (a,b)
type a ⊸ b = a -> b

infixr ⊸
type Effect = IO () -- for simplicity
-- instance Monoid Effect

type N a = a ⊸ Effect

newtype Bang a = Bang a


data MutableByteArray = MBA {-ω-}Int {-ω-}(Ptr CChar)

newtype ByteArray = BA MutableByteArray

class Data a where
  copy :: a -> a
instance Data CChar where
  copy x = x

withNewByteArray :: (Data k) => Int -> (MutableByteArray ⊸ k) ⊸ k
withNewByteArray n f = copy $ unsafePerformIO $
  allocaArray n (return . f . MBA n)

updateByteArray :: Int -> CChar -> MutableByteArray ⊸ MutableByteArray
updateByteArray n byte (MBA size ar) = unsafePerformIO $ do
  pokeElemOff ar n byte
  return $ MBA size ar

freeByteArray :: MutableByteArray ⊸ ()
freeByteArray (MBA _ ar) = unsafePerformIO $ free ar

freezeByteArray :: MutableByteArray ⊸ Bang ByteArray
freezeByteArray (MBA size ar) = Bang (BA (MBA size ar))

indexByteArray :: Int -> ByteArray -> CChar
indexByteArray i (BA (MBA size ar)) = unsafePerformIO $
  peekElemOff ar i

