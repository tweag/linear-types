{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

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
import qualified Socket.Generic as G
import Socket.Generic (SocketAddress, State(..))
import qualified System.Socket as S
import qualified System.Socket.Family.Inet6 as S
import qualified System.Socket.Type.Stream as S
import qualified System.Socket.Protocol.TCP as S

type Socket (s :: State) = G.Socket S.TCP s

-- | Typestate automaton for TCP
type instance G.Initial S.TCP = 'Unbound
instance G.Rule S.TCP "bind" 'Unbound 'Bound
instance G.Rule S.TCP "listen" 'Bound 'Listening
instance G.Rule S.TCP "accept" 'Listening 'Listening
instance G.Rule S.TCP "connect" 'Unbound 'Ingress
instance G.Rule S.TCP "send" 'Ingress 'Ingress
instance G.Rule S.TCP "receive" 'Egress 'Egress

socket ::  IO' 'One (Socket 'Unbound)
socket = G.socket

bind ::  Socket 'Unbound ⊸ SocketAddress -> IO' 'One (Socket 'Bound)
bind = G.bind

listen :: Socket 'Bound ⊸ IO' 'One (Socket 'Listening)
listen = G.listen

accept ::  Socket 'Listening ⊸ IO' 'One (Socket 'Listening, Socket 'Egress)
accept = G.accept

connect ::  Socket 'Unbound ⊸ SocketAddress -> IO' 'One (Socket 'Ingress)
connect = G.connect

send :: Socket 'Ingress ⊸ ByteString -> IO' 'One (Socket 'Ingress, Unrestricted Int)
send = G.send

receive :: Socket 'Egress ⊸ IO' 'One (Socket 'Egress, Unrestricted ByteString)
receive = G.receive

close :: forall s. Socket s -> IO' 'Ω ()
close = G.close
