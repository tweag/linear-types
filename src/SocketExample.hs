{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

-- | This short example is based on the hello-world example of the socket
-- library which can be found here:
--
-- https://github.com/lpeterse/haskell-socket/blob/0136260f1baf0a7114f41cf6e773396c4856c1d6/examples/HelloWorldServer.hs
--

module SocketExample where

import Data.ByteString.Char8 ()
import Data.String (String, fromString)
import IO
import Linear.Std
import Prelude (fromInteger, (++), show)
import qualified Prelude as P
import Socket
import Socket.Generic (State(..))
import qualified System.Socket as S
import qualified System.Socket.Family.Inet6 as S
import qualified System.Socket.Type.Stream as S
import qualified System.Socket.Protocol.TCP as S

forever :: (a ⊸ IO' 'One a) -> a ⊸ IO' 'Ω b
forever f a = do
  a' <- f a
  forever f a'

putStrLn :: String -> IO' 'Ω ()
putStrLn s = unsafeIOtoIOΩ (P.putStrLn s)

main :: IO' 'Ω a
main = do
  s1 <- socket
  s2 <- bind s1 (S.SocketAddressInet6 S.inet6Any 8080 0 0)
  s3 <- listen s2
  putStrLn "Listening socket ready..."
  forever acceptAndHandle s3

acceptAndHandle :: Socket 'Listening ⊸ IO' 'One (Socket 'Listening)
acceptAndHandle s = do
  (s', p1) <- accept s
  putStrLn $ "Accepted connection"
  (p2, Unrestricted _) <- send p1 "Hello world!"
  close p2
  returnL s'
