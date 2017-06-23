{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Socket where

-- | Sockets follow a rather long-winded protocol which looks like:
--   * Receiving end: create -> bind -> listen -> accept -> receive
--   * Sending end: create -> connect -> send
--
-- This module implements this protocol in type-states using linear type. We
-- follow a simplified version of the api in the @socket@ library (assuming only
-- tcp sockets).

import Data.ByteString (ByteString)
import IO hiding (return)
import Linear.Std
import Linear.Unsafe (unsafeUnrestricted)
import Prelude hiding (($))
import qualified System.Socket as S
import qualified System.Socket.Family.Inet6 as S
import qualified System.Socket.Type.Stream as S
import qualified System.Socket.Protocol.TCP as S

-- TODO: newtype, for abstraction
type Socket (s :: State) = S.Socket S.Inet6 S.Stream S.TCP
type SocketAddress = S.SocketAddress S.Inet6
data State
  = Unbound
  | Bound
  | Listening
  | Ingress
  | Egress

socket ::  IO' 'One (Socket 'Unbound)
socket = unsafeIOtoIO1 S.socket

bind ::  Socket 'Unbound ⊸ SocketAddress -> IO' 'One (Socket 'Bound)
bind sock addr = unsafeIOtoIO1 (unsafeBind (unsafeUnrestricted (sock, addr)))
  where
    unsafeBind :: Unrestricted (Socket 'Unbound,SocketAddress) ⊸ IO (Socket 'Bound)
    unsafeBind (Unrestricted (sock, addr)) = do
      S.bind sock addr
      return sock

listen :: Socket 'Bound ⊸ IO' 'One (Socket 'Listening)
listen sock = unsafeIOtoIO1 (unsafeListen (unsafeUnrestricted sock))
  where
    unsafeListen :: Unrestricted (Socket 'Bound) ⊸ IO (Socket 'Listening)
    unsafeListen (Unrestricted sock) = do
      S.listen sock 0
      return sock

accept ::  Socket 'Listening ⊸ IO' 'One (Socket 'Listening, Socket 'Egress)
accept sock = unsafeIOtoIO1 (unsafeAccept (unsafeUnrestricted sock))
  where
    unsafeAccept :: Unrestricted (Socket 'Listening) ⊸ IO (Socket 'Listening, Socket 'Egress)
    unsafeAccept (Unrestricted sock) = do
      (incoming, _) <- S.accept sock
      return (sock, incoming)

connect ::  Socket 'Unbound ⊸ SocketAddress -> IO' 'One (Socket 'Ingress)
connect sock addr = unsafeIOtoIO1 (unsafeConnect (unsafeUnrestricted (sock, addr)))
  where
    unsafeConnect :: Unrestricted (Socket 'Unbound, SocketAddress) ⊸ IO (Socket 'Ingress)
    unsafeConnect (Unrestricted (sock, addr)) = do
      S.connect sock addr
      return sock

send :: Socket 'Ingress ⊸ ByteString -> IO' 'One (Socket 'Ingress, Unrestricted Int)
send sock chunk = unsafeIOtoIO1 (unsafeSend (unsafeUnrestricted sock))
  where
    unsafeSend :: Unrestricted (Socket 'Ingress) ⊸ IO (Socket 'Ingress, Unrestricted Int)
    unsafeSend (Unrestricted sock) = do
      nbytes <- S.send sock chunk mempty
      return (sock, Unrestricted nbytes)

receive :: Socket 'Egress ⊸ IO' 'One (Socket 'Egress, Unrestricted ByteString)
receive sock = unsafeIOtoIO1 (unsafeReceive (unsafeUnrestricted sock))
  where
    unsafeReceive :: Unrestricted (Socket 'Egress) ⊸ IO (Socket 'Egress, Unrestricted ByteString)
    unsafeReceive (Unrestricted sock) = do
      chunk <- S.receive sock 4096 mempty
      return (sock, Unrestricted chunk)

close :: forall s. Socket s -> IO' 'Ω ()
close sock = unsafeIOtoIOΩ (unsafeClose (unsafeUnrestricted sock))
  where
    unsafeClose :: Unrestricted (Socket s) ⊸ IO ()
    unsafeClose (Unrestricted sock) = S.close sock
