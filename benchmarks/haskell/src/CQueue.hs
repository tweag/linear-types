{-# LANGUAGE ForeignFunctionInterface #-}
module CQueue where

import Foreign.C 
import Foreign.Ptr (Ptr,nullPtr)

foreign import ccall "sin" c_sin :: CDouble -> CDouble
-- foreign import ccall "create_queue" CCreateQueue :: CQueue
-- foreign import ccall "push" CPush :: Ptr CQueue -> CInt -> ()
-- foreign import ccall "pop" CPop :: Ptr CQueue -> Ptr CNode

tutu :: IO ()
tutu = print "toto"
