{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Socket where

-- | Sockets follow a rather long-winded protocol which looks like:
--   * Receiving end: create -> bind -> listen -> accept -> receive
--   * Sending end: create -> connect -> send
--
-- This module implements this protocol in type-states using linear type. We
-- follow a simplified version of the api in the @socket@ library (assuming only
-- tcp sockets).

import Data.ByteString (ByteString)
import IO
import Linear.Std
import Prelude hiding (($))

data Socket = Socket
data SocketAddress = SocketAddress

socket ::  IO' 'One (Socket)
socket = error "TODO: Socket.socket"

connect ::  Socket ⊸ SocketAddress -> IO' 'One (Socket)
connect = error "TODO: Socket.connect"

bind ::  Socket ⊸ SocketAddress -> IO' 'One (Socket)
bind = error "TODO: Socket.bind"

listen :: Socket ⊸ IO' 'One (Socket)
listen = error "TODO: Socket.listen"

accept ::  Socket ⊸ IO' 'One (Socket, Socket)
accept = error "TODO: Socket.accept"

send :: Socket ⊸ ByteString -> IO' 'One (Socket, Unrestricted Int)
send = error "TODO: Socket.send"

receive :: Socket ⊸ IO' 'One (Socket, ByteString)
receive = error "TODO: Socket.send"

close :: Socket -> IO' 'Ω ()
close = error "TODO: Socket.close"
