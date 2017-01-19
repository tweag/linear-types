{-# LANGUAGE ForeignFunctionInterface #-}

module CQueue where

import Foreign.C 
import Foreign.Ptr (Ptr,nullPtr)

type NodePtr = Int
type QueuePtr = Int

foreign import ccall "pop" c_pop :: QueuePtr -> IO NodePtr
foreign import ccall "push" c_push :: QueuePtr -> Int -> IO ()
foreign import ccall "clear_queue" c_clear_queue :: QueuePtr -> IO ()
foreign import ccall "create_queue" c_create_queue :: IO QueuePtr
foreign import ccall "delete_node" c_delete_node :: QueuePtr -> Int -> IO Int
foreign import ccall "print_queue" c_print_queue :: QueuePtr -> IO ()
