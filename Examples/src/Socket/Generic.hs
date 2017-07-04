{-# LANGUAGE AllowAmbiguousTypes #-} -- TODO: probably because Socket is not a newtype. FIXME at some point
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Socket.Generic where

-- | Sockets follow a rather long-winded protocol which looks like:
--   * Receiving end: create -> bind -> listen -> accept -> receive
--   * Sending end: create -> connect -> send
-- But can differ depending on the protocol.
--
-- This module provides a protocol-parametric API for socket. Each protocol can
-- declare rules in the form of a deterministic finite automaton to enforce the
-- appropriate protocol

import Data.ByteString (ByteString)
import Data.Coerce
import GHC.TypeLits (Symbol)
import IO hiding (return)
import Linear.Std
import Linear.Unsafe (unsafeUnrestricted)
import Prelude hiding (($))
import qualified System.Socket as S
import qualified System.Socket.Family.Inet6 as S
import qualified System.Socket.Type.Stream as S
import qualified System.Socket.Protocol.TCP as S

newtype Socket p (s :: State) = S { unS :: S.Socket S.Inet6 S.Stream p}
type S p = S.Socket S.Inet6 S.Stream p
type SocketAddress = S.SocketAddress S.Inet6
-- TODO: this should be abstract too, in a type family
data State
  = Unbound
  | Bound
  | Listening
  | Connected

-- Initial state of the protocol
type family Initial p :: State

-- Transition rules of the automaton, the second argument is named after the
-- function that it applies to. The first argument is the protocol this rule
-- applies to.
class Rule p (action :: Symbol) (pre :: State) (post :: State) | p action pre -> post

socket :: forall p. S.Protocol p => IO' 'One (Socket p (Initial p))
socket = coerce $ unsafeIOtoIO1 (S.socket :: IO (S p))

bind :: forall p pre post. Rule p "bind" pre post => Socket p pre ⊸ SocketAddress -> IO' 'One (Socket p post)
bind sock addr = unsafeIOtoIO1 (unsafeBind (unsafeUnrestricted (sock, addr)))
  where
    unsafeBind :: Unrestricted (Socket p pre,SocketAddress) ⊸ IO (Socket p post)
    unsafeBind (Unrestricted (coerce -> sock, addr)) = do
      S.bind sock addr
      return (coerce sock)

listen :: forall p pre post. Rule p "listen" pre post => Socket p pre ⊸ IO' 'One (Socket p post)
listen sock = unsafeIOtoIO1 (unsafeListen (unsafeUnrestricted sock))
  where
    unsafeListen :: Unrestricted (Socket p pre) ⊸ IO (Socket p post)
    unsafeListen (Unrestricted (coerce -> sock)) = do
      S.listen sock 0
      return (coerce sock)

accept :: forall p pre post. Rule p "accept" pre post => Socket p pre ⊸ IO' 'One (Socket p post, Socket p 'Connected)
accept sock = unsafeIOtoIO1 (unsafeAccept (unsafeUnrestricted sock))
  where
    unsafeAccept :: Unrestricted (Socket p pre) ⊸ IO (Socket p post, Socket p 'Connected)
    unsafeAccept (Unrestricted (coerce -> sock)) = do
      (incoming, _) <- S.accept (sock :: S p)
      return (coerce sock, coerce incoming)

connect :: forall p pre post. Rule p "connect" pre post => Socket p pre ⊸ SocketAddress -> IO' 'One (Socket p post)
connect sock addr = unsafeIOtoIO1 (unsafeConnect (unsafeUnrestricted (sock, addr)))
  where
    unsafeConnect :: Unrestricted (Socket p pre, SocketAddress) ⊸ IO (Socket p post)
    unsafeConnect (Unrestricted (coerce -> sock, addr)) = do
      S.connect sock addr
      return $ coerce sock

send :: forall p pre post. Rule p "send" pre post => Socket p pre ⊸ ByteString -> IO' 'One (Socket p post, Unrestricted Int)
send sock chunk = unsafeIOtoIO1 (unsafeSend (unsafeUnrestricted sock))
  where
    unsafeSend :: Unrestricted (Socket p pre) ⊸ IO (Socket p post, Unrestricted Int)
    unsafeSend (Unrestricted (coerce -> sock)) = do
      nbytes <- S.send sock chunk mempty
      return (coerce sock, Unrestricted nbytes)

receive :: forall p pre post. Rule p "receive" pre post => Socket p pre ⊸ IO' 'One (Socket p post, Unrestricted ByteString)
receive sock = unsafeIOtoIO1 (unsafeReceive (unsafeUnrestricted sock))
  where
    unsafeReceive :: Unrestricted (Socket p pre) ⊸ IO (Socket p post, Unrestricted ByteString)
    unsafeReceive (Unrestricted (coerce -> sock)) = do
      chunk <- S.receive sock 4096 mempty
      return (coerce sock, Unrestricted chunk)

-- We could also have precondition for close
close :: forall p s. Socket p s -> IO' 'Ω ()
close sock = unsafeIOtoIOΩ (unsafeClose (unsafeUnrestricted sock))
  where
    unsafeClose :: Unrestricted (Socket p s) ⊸ IO ()
    unsafeClose (Unrestricted (coerce -> sock)) = S.close sock
