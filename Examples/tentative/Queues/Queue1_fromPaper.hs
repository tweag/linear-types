{-# LANGUAGE TypeOperators #-}

-- | This first version of the linear queue API is what appeared in the first draft of the paper:

module Queue1 where
    
-- The two character token "-o" is not valid, so just use this to mark
-- linear arrows for now:
type (⊸) = (->)
    
data Queue
data Msg
data Vector a    
newtype Bang a = Bang a

alloc   :: (Queue ⊸ Bang a) ⊸ a
free    :: Queue ⊸ ()

push    :: Msg -> Queue ⊸ Queue
delete  :: Msg -> Queue ⊸ Queue
evict   :: Int -> Queue ⊸ (Queue, Bang (Vector Msg))

alloc = undefined
free = undefined
push = undefined
delete = undefined
evict = undefined
