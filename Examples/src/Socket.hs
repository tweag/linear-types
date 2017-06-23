{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
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

data Socket (s :: State) = Socket
data SocketAddress = SocketAddress
data State
  = Unbound
  | Bound
  | Listening
  | Ingress
  | Egress

socket ::  IO' 'One (Socket 'Unbound)
socket = error "TODO: Socket.socket"

bind ::  Socket 'Unbound ⊸ SocketAddress -> IO' 'One (Socket 'Bound)
bind = error "TODO: Socket.bind"

listen :: Socket 'Bound ⊸ IO' 'One (Socket 'Listening)
listen = error "TODO: Socket.listen"

accept ::  Socket 'Listening ⊸ IO' 'One (Socket 'Listening, Socket 'Egress)
accept = error "TODO: Socket.accept"

connect ::  Socket 'Unbound ⊸ SocketAddress -> IO' 'One (Socket 'Ingress)
connect = error "TODO: Socket.connect"

send :: Socket 'Ingress ⊸ ByteString -> IO' 'One (Socket 'Ingress, Unrestricted Int)
send = error "TODO: Socket.send"

receive :: Socket 'Egress ⊸ IO' 'One (Socket 'Egress, ByteString)
receive = error "TODO: Socket.send"

close :: Socket s -> IO' 'Ω ()
close = error "TODO: Socket.close"
