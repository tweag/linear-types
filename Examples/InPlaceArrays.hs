-- This example proposed an API for manipulation of arrays with
-- in-place updates.

{-# LANGUAGE TypeOperators #-}
module Calculator where
import Data.Monoid

-- Broken man's linear types.
type a ⊗ b = (a,b)
type a ⊸ b = a -> b

data Bang a where
  Box :: a → Bang a

class Data a where
  copy :: a ⊸ Bang a


type Heap -- abstract; this gives a reference to a primitive
          -- heap.

heap ::1 Heap -- there is only one heap; so the implementation may use
              -- a global variable for this, in which case the Heap
              -- type has no runtime representation

type Array index element -- may be represented by a single pointer

alloc :: Heap ⊸ (Array i a ⊗ Heap)
free :: Array i a ⊸ Heap ⊸ Heap

index :: Data a => i -> Array i a ⊸ (a ⊗ Array i a)
update :: Data a => i -> a -> Array i a ⊸ Array i a
-- can be implemented as an 'in-place' update

split :: i -> Array i a ⊸ (Array i a ⊗ Array i a)

